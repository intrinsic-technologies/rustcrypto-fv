import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l104370 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104370 bytes_l104370) (entryMap (live .l104370))
      15 0x104370 bytes_l104370 b_l104370 := by
  have f0 : InstrSpec 0x104370 [0x55] (PushPre 0x104370 1) (pushR64Effect 0x104370 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104370 1 5).toInstrSpec (push_r64_effect_step 0x104370 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x104371 [0x41, 0x57] (PushPre 0x104371 2) (pushR64Effect 0x104371 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104371 2 15).toInstrSpec (push_r64_rex_effect_step 0x104371 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x104373 [0x41, 0x56] (PushPre 0x104373 2) (pushR64Effect 0x104373 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104373 2 14).toInstrSpec (push_r64_rex_effect_step 0x104373 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x104375 [0x41, 0x55] (PushPre 0x104375 2) (pushR64Effect 0x104375 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104375 2 13).toInstrSpec (push_r64_rex_effect_step 0x104375 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x104377 [0x41, 0x54] (PushPre 0x104377 2) (pushR64Effect 0x104377 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104377 2 12).toInstrSpec (push_r64_rex_effect_step 0x104377 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x104379 [0x53] (PushPre 0x104379 1) (pushR64Effect 0x104379 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104379 1 3).toInstrSpec (push_r64_effect_step 0x104379 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10437a [0x48, 0x81, 0xEC, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10437a) (subR64Imm32Effect 0x10437a 4 0xd8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10437a 4 0xd8).toInstrSpec (sub_r64_imm32_effect_step 0x10437a 0x48 0xec 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104381 [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x104381) (movR64R64Effect 0x104381 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x104381 12 6).toInstrSpec (mov_r64_r64_effect_step 0x104381 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x104384 [0x48, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00] (StorePre 0x104384 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x104384 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x104384 7 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x104384 7 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x104384 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10438c [0x4C, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x10438c) (leaR64Effect 0x10438c 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x10438c 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x10438c 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x104391 [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x104391) (xorR32R32Effect 0x104391 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104391 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x104391 0x45 0xff (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x104394 [0xBA, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104394) (movR32Imm32Effect 0x104394 5 2 0xb0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x104394 5 2 0xb0).toInstrSpec (mov_r32_imm32_effect_step 0x104394 0xba (by decide) 0xb0) pre_rip
  have f12 : InstrSpec 0x104399 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x104399) (movR64R64Effect 0x104399 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104399 7 14).toInstrSpec (mov_r64_r64_effect_step 0x104399 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10439c [0x31, 0xF6] (fun s => s.RIP = 0x10439c) (xorR32R32Effect 0x10439c 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10439c 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x10439c 0xf6 (by decide)) pre_rip
  have f14 : InstrSpec 0x10439e [0xFF, 0x15, 0x84, 0xCE, 0x0F, 0x00] (GoesTo (CallMemPre 0x10439e (.rip 0xfce84)) (callEffect (callMemPtr 0x10439e (.rip 0xfce84)) (0x10439e + BitVec.ofNat 64 (callMemLen (.rip 0xfce84)))) 0x103eb0) (callEffect (callMemPtr 0x10439e (.rip 0xfce84)) (0x10439e + BitVec.ofNat 64 (callMemLen (.rip 0xfce84))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x10439e (.rip 0xfce84)).toInstrSpec (call_m64_effect_step 0x10439e (.rip 0xfce84) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103eb0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104371) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104373) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104375) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104377) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104379) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10437a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104381) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104384) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10438c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104391) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104394) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(2, 74), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104399) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(2, 74), (3, 3), (4, 65), (5, 5), (6, 6), (7, 76), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10439c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(2, 74), (3, 3), (4, 65), (5, 5), (6, 78), (7, 76), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10439e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(2, 74), (3, 3), (4, 80), (5, 5), (6, 78), (7, 76), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 72), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb0) f14 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 82) (by decide) (by decide) rfl rfl

theorem block_l104370 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104370 :=
  Rest.liftedBlock (rest_l104370 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104370 x hx)

theorem rest_l1043a4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1043a4 bytes_l1043a4) (entryMap (live .l1043a4))
      8 0x1043a4 bytes_l1043a4 b_l1043a4 := by
  have f0 : InstrSpec 0x1043a4 [0x49, 0x8B, 0x04, 0x24] (LoadPre 0x1043a4 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1043a4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1043a4 0 (.sib 12 none 0 .none))
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1043a4 0 (.sib 12 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1043a4 0x49 (by decide) 0 (.sib 12 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1043a8 [0x49, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x1043a8 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x1043a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1043a8 1 (.sib 12 none 0 (.d8 0x8)))
      [.gpr 12] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1043a8 1 (.sib 12 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1043a8 0x49 (by decide) 1 (.sib 12 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1043ad [0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00] (StorePre 0x1043ad 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1043ad + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1043ad 1 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1043ad 1 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_m64_r64_effect_step 0x1043ad 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1043b5 [0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] (StorePre 0x1043b5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1043b5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1043b5 0 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1043b5 0 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1043b5 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1043bd [0x48, 0x8D, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1043bd) (leaR64Effect 0x1043bd 2 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1043bd 2 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (lea_r64_effect_step 0x1043bd 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1043c5 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1043c5) (movR32Imm32Effect 0x1043c5 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1043c5 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x1043c5 0xbe (by decide) 0x8) pre_rip
  have f6 : InstrSpec 0x1043ca [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1043ca) (movR64R64Effect 0x1043ca 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1043ca 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1043ca 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1043cd [0xE8, 0x1E, 0x5C, 0x00, 0x00] (PushPre 0x1043cd 5) (callEffect (fun _ => 0x109ff0) 0x1043d2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1043cd 0x109ff0 0x1043d2).toInstrSpec (call_rel32_effect_step 0x1043cd 0x5c1e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043a8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043ad) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043b5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043bd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043c5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043ca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 4), (5, 5), (6, 61), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043cd) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 55), (2, 59), (3, 3), (4, 65), (5, 5), (6, 61), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff0) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l1043a4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1043a4 :=
  Rest.liftedBlock (rest_l1043a4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1043a4 x hx)

theorem rest_l1043d2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1043d2 bytes_l1043d2) (entryMap (live .l1043d2))
      4 0x1043d2 bytes_l1043d2 b_l1043d2 := by
  have f0 : InstrSpec 0x1043d2 [0x41, 0xBC, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1043d2) (movR32Imm32Effect 0x1043d2 6 12 0x10)
      [] [] [.reg 12, .rip] :=
    (movR32Imm32Effect_footprint 0x1043d2 6 12 0x10).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1043d2 0x41 0xbc (by decide) (by decide) 0x10) pre_rip
  have f1 : InstrSpec 0x1043d8 [0x4D, 0x89, 0xF5] (fun s => s.RIP = 0x1043d8) (movR64R64Effect 0x1043d8 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1043d8 13 14).toInstrSpec (mov_r64_r64_effect_step 0x1043d8 0x4d 0xf5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1043db [0x31, 0xED] (fun s => s.RIP = 0x1043db) (xorR32R32Effect 0x1043db 2 5 5)
      [.gpr 5, .gpr 5] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1043db 2 5 5).toInstrSpec (xor_r32_r32_effect_step 0x1043db 0xed (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 53), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043db) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (11, 11), (12, 53), (13, 55), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043dd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel8_effect_step 0x1043dd 0x45 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1043d2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1043d2 :=
  Rest.liftedBlock (rest_l1043d2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1043d2 x hx)

theorem rest_l1043e0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1043e0 bytes_l1043e0) (entryMap (live .l1043e0))
      4 0x1043e0 bytes_l1043e0 b_l1043e0 := by
  have f0 : InstrSpec 0x1043e0 [0x41, 0x80, 0x75, 0x00, 0x80] (StorePre 0x1043e0 5 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1043e0 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1043e0 5 (.base 13 (.d8 0x0)) 0x80)
      [.gpr 13] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1043e0 5 (.base 13 (.d8 0x0)) 0x80).toInstrSpec (xor_m8_imm8_rex_effect_step 0x1043e0 0x41 (by decide) (.base 13 (.d8 0x0)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1043e5 [0x41, 0x80, 0x75, 0x02, 0x80] (StorePre 0x1043e5 5 (fun s => AddrMode.addr (.base 13 (.d8 0x2)) s (0x1043e5 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1043e5 5 (.base 13 (.d8 0x2)) 0x80)
      [.gpr 13] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1043e5 5 (.base 13 (.d8 0x2)) 0x80).toInstrSpec (xor_m8_imm8_rex_effect_step 0x1043e5 0x41 (by decide) (.base 13 (.d8 0x2)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1043ea [0x41, 0x80, 0x75, 0x06, 0x80] (StorePre 0x1043ea 5 (fun s => AddrMode.addr (.base 13 (.d8 0x6)) s (0x1043ea + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1043ea 5 (.base 13 (.d8 0x6)) 0x80)
      [.gpr 13] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1043ea 5 (.base 13 (.d8 0x6)) 0x80).toInstrSpec (xor_m8_imm8_rex_effect_step 0x1043ea 0x41 (by decide) (.base 13 (.d8 0x6)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1043ef [0x41, 0x80, 0x75, 0x08, 0x80] (StorePre 0x1043ef 5 (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x1043ef + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x1043ef 5 (.base 13 (.d8 0x8)) 0x80)
      [.gpr 13] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x1043ef 5 (.base 13 (.d8 0x8)) 0x80).toInstrSpec (xor_m8_imm8_rex_effect_step 0x1043ef 0x41 (by decide) (.base 13 (.d8 0x8)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043e5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043ea) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043ef) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043f4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 57) (by decide) rfl

theorem block_l1043e0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1043e0 :=
  Rest.liftedBlock (rest_l1043e0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1043e0 x hx)

theorem rest_l1043f4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1043f4 bytes_l1043f4) (entryMap (live .l1043f4))
      7 0x1043f4 bytes_l1043f4 b_l1043f4 := by
  have f0 : InstrSpec 0x1043f4 [0x49, 0x83, 0xC7, 0x08] (fun s => s.RIP = 0x1043f4) (addR64Imm8Effect 0x1043f4 15 0x8)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1043f4 15 0x8).toInstrSpec (add_r64_imm8_effect_step 0x1043f4 0x49 0xc7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1043f8 [0xBE, 0x58, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1043f8) (movR32Imm32Effect 0x1043f8 5 6 0x58)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1043f8 5 6 0x58).toInstrSpec (mov_r32_imm32_effect_step 0x1043f8 0xbe (by decide) 0x58) pre_rip
  have f2 : InstrSpec 0x1043fd [0xB9, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1043fd) (movR32Imm32Effect 0x1043fd 5 1 0x8)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x1043fd 5 1 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x1043fd 0xb9 (by decide) 0x8) pre_rip
  have f3 : InstrSpec 0x104402 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x104402) (movR64R64Effect 0x104402 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104402 7 14).toInstrSpec (mov_r64_r64_effect_step 0x104402 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104405 [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x104405) (movR64R64Effect 0x104405 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x104405 2 15).toInstrSpec (mov_r64_r64_effect_step 0x104405 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104408 [0x41, 0xB8, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104408) (movR32Imm32Effect 0x104408 6 8 0x7)
      [] [] [.reg 8, .rip] :=
    (movR32Imm32Effect_footprint 0x104408 6 8 0x7).toInstrSpec (mov_r32_imm32_rex_effect_step 0x104408 0x41 0xb8 (by decide) (by decide) 0x7) pre_rip
  have f6 : InstrSpec 0x10440e [0xE8, 0xFD, 0xFB, 0xFF, 0xFF] (PushPre 0x10440e 5) (callEffect (fun _ => 0x104010) 0x104413)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10440e 0x104010 0x104413).toInstrSpec (call_rel32_effect_step 0x10440e 0xfffffbfd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043f8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1043fd) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104402) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104405) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104408) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 57), (2, 61), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10440e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 57), (2, 61), (3, 3), (4, 65), (5, 5), (6, 55), (7, 59), (8, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104010) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 67) (by decide) (by decide) rfl rfl

theorem block_l1043f4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1043f4 :=
  Rest.liftedBlock (rest_l1043f4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1043f4 x hx)

theorem rest_l104413 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104413 bytes_l104413) (entryMap (live .l104413))
      5 0x104413 bytes_l104413 b_l104413 := by
  have f0 : InstrSpec 0x104413 [0x49, 0x83, 0xC5, 0x12] (fun s => s.RIP = 0x104413) (addR64Imm8Effect 0x104413 13 0x12)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104413 13 0x12).toInstrSpec (add_r64_imm8_effect_step 0x104413 0x49 0xc5 0x12 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104417 [0x49, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x104417) (addR64Imm8Effect 0x104417 12 0x10)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104417 12 0x10).toInstrSpec (add_r64_imm8_effect_step 0x104417 0x49 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10441b [0x48, 0xFF, 0xC5] (fun s => s.RIP = 0x10441b) (incR64Effect 0x10441b 5)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (incR64Effect_footprint 0x10441b 5).toInstrSpec (inc_r64_effect_step 0x10441b 0x48 0xc5 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10441e [0x49, 0x83, 0xFF, 0x50] (fun s => s.RIP = 0x10441e) (cmpR64Imm8Effect 0x10441e 15 0x50)
      [.gpr 15] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10441e 15 0x50).toInstrSpec (cmp_r64_imm8_effect_step 0x10441e 0x49 0xff 0x50 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104417) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10441b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10441e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (11, 11), (12, 55), (13, 53), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104422) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel8_effect_step 0x104422 4 0x4b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104413 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104413 :=
  Rest.liftedBlock (rest_l104413 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104413 x hx)

theorem rest_l104424 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104424 bytes_l104424) (entryMap (live .l104424))
      4 0x104424 bytes_l104424 b_l104424 := by
  have f0 : InstrSpec 0x104424 [0xBE, 0x58, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104424) (movR32Imm32Effect 0x104424 5 6 0x58)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x104424 5 6 0x58).toInstrSpec (mov_r32_imm32_effect_step 0x104424 0xbe (by decide) 0x58) pre_rip
  have f1 : InstrSpec 0x104429 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x104429) (movR64R64Effect 0x104429 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x104429 7 14).toInstrSpec (mov_r64_r64_effect_step 0x104429 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10442c [0x4C, 0x89, 0xFA] (fun s => s.RIP = 0x10442c) (movR64R64Effect 0x10442c 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10442c 2 15).toInstrSpec (mov_r64_r64_effect_step 0x10442c 0x4c 0xfa (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10442f [0xE8, 0xFC, 0xFA, 0xFF, 0xFF] (PushPre 0x10442f 5) (callEffect (fun _ => 0x103f30) 0x104434)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10442f 0x103f30 0x104434).toInstrSpec (call_rel32_effect_step 0x10442f 0xfffffafc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104429) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10442c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10442f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f30) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l104424 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104424 :=
  Rest.liftedBlock (rest_l104424 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104424 x hx)

theorem rest_l104434 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104434 bytes_l104434) (entryMap (live .l104434))
      4 0x104434 bytes_l104434 b_l104434 := by
  have f0 : InstrSpec 0x104434 [0x4A, 0x8D, 0x3C, 0x24] (fun s => s.RIP = 0x104434) (leaR64Effect 0x104434 7 (.sib 4 (some 12) 0 .none))
      [.gpr 4, .gpr 12] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x104434 7 (.sib 4 (some 12) 0 .none)).toInstrSpec (lea_r64_effect_step 0x104434 0x4a (by decide) 7 (.sib 4 (some 12) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104438 [0x48, 0x83, 0xC7, 0x08] (fun s => s.RIP = 0x104438) (addR64Imm8Effect 0x104438 7 0x8)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x104438 7 0x8).toInstrSpec (add_r64_imm8_effect_step 0x104438 0x48 0xc7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10443c [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10443c) (movR32Imm32Effect 0x10443c 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10443c 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x10443c 0xbe (by decide) 0x8) pre_rip
  have f3 : InstrSpec 0x104441 [0xE8, 0xCA, 0xC6, 0xFF, 0xFF] (PushPre 0x104441 5) (callEffect (fun _ => 0x100b10) 0x104446)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104441 0x100b10 0x104446).toInstrSpec (call_rel32_effect_step 0x104441 0xffffc6ca (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104438) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10443c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104441) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f3 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 61) (by decide) (by decide) rfl rfl

theorem block_l104434 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104434 :=
  Rest.liftedBlock (rest_l104434 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104434 x hx)

theorem rest_l104446 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104446 bytes_l104446) (entryMap (live .l104446))
      6 0x104446 bytes_l104446 b_l104446 := by
  have f0 : InstrSpec 0x104446 [0x66, 0x42, 0xF7, 0x54, 0x7C, 0x18] (StorePre 0x104446 6 (fun s => AddrMode.addr (.sib 4 (some 15) 1 (.d8 0x18)) s (0x104446 + BitVec.ofNat 64 6)) 2) (notMEffect 0x104446 6 16 (.sib 4 (some 15) 1 (.d8 0x18)))
      [.gpr 4, .gpr 15] [] [.rip] :=
    (notMEffect16_footprint 0x104446 6 (.sib 4 (some 15) 1 (.d8 0x18))).toInstrSpec (not_m16_rex_effect_step 0x104446 0x42 (by decide) (.sib 4 (some 15) 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x10444c [0x66, 0x42, 0xF7, 0x54, 0x7C, 0x1A] (StorePre 0x10444c 6 (fun s => AddrMode.addr (.sib 4 (some 15) 1 (.d8 0x1a)) s (0x10444c + BitVec.ofNat 64 6)) 2) (notMEffect 0x10444c 6 16 (.sib 4 (some 15) 1 (.d8 0x1a)))
      [.gpr 4, .gpr 15] [] [.rip] :=
    (notMEffect16_footprint 0x10444c 6 (.sib 4 (some 15) 1 (.d8 0x1a))).toInstrSpec (not_m16_rex_effect_step 0x10444c 0x42 (by decide) (.sib 4 (some 15) 1 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x104452 [0x66, 0x42, 0xF7, 0x54, 0x7C, 0x22] (StorePre 0x104452 6 (fun s => AddrMode.addr (.sib 4 (some 15) 1 (.d8 0x22)) s (0x104452 + BitVec.ofNat 64 6)) 2) (notMEffect 0x104452 6 16 (.sib 4 (some 15) 1 (.d8 0x22)))
      [.gpr 4, .gpr 15] [] [.rip] :=
    (notMEffect16_footprint 0x104452 6 (.sib 4 (some 15) 1 (.d8 0x22))).toInstrSpec (not_m16_rex_effect_step 0x104452 0x42 (by decide) (.sib 4 (some 15) 1 (.d8 0x22)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x104458 [0x66, 0x42, 0xF7, 0x54, 0x7C, 0x24] (StorePre 0x104458 6 (fun s => AddrMode.addr (.sib 4 (some 15) 1 (.d8 0x24)) s (0x104458 + BitVec.ofNat 64 6)) 2) (notMEffect 0x104458 6 16 (.sib 4 (some 15) 1 (.d8 0x24)))
      [.gpr 4, .gpr 15] [] [.rip] :=
    (notMEffect16_footprint 0x104458 6 (.sib 4 (some 15) 1 (.d8 0x24))).toInstrSpec (not_m16_rex_effect_step 0x104458 0x42 (by decide) (.sib 4 (some 15) 1 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10445e [0x48, 0x83, 0xFD, 0x08] (fun s => s.RIP = 0x10445e) (cmpR64Imm8Effect 0x10445e 5 0x8)
      [.gpr 5] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10445e 5 0x8).toInstrSpec (cmp_r64_imm8_effect_step 0x10445e 0x48 0xfd 0x8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10444c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104452) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104458) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10445e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104462) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x104462 3 0xffffff78) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104446 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104446 :=
  Rest.liftedBlock (rest_l104446 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104446 x hx)

theorem rest_l104468 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104468 bytes_l104468) (entryMap (live .l104468))
      2 0x104468 bytes_l104468 b_l104468 := by
  have f0 : InstrSpec 0x104468 [0x41, 0x80, 0x75, 0x10, 0x80] (StorePre 0x104468 5 (fun s => AddrMode.addr (.base 13 (.d8 0x10)) s (0x104468 + BitVec.ofNat 64 5)) 1) (xorM8Imm8Effect 0x104468 5 (.base 13 (.d8 0x10)) 0x80)
      [.gpr 13] [] [.flags, .rip] :=
    (xorM8Imm8Effect_footprint 0x104468 5 (.base 13 (.d8 0x10)) 0x80).toInstrSpec (xor_m8_imm8_rex_effect_step 0x104468 0x41 (by decide) (.base 13 (.d8 0x10)) (by decide) (by decide) (by decide) 0x80) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10446d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel8_effect_step 0x10446d 0x85 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l104468 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104468 :=
  Rest.liftedBlock (rest_l104468 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104468 x hx)

theorem rest_l10446f_41 [Bindings] (code : CodeMap) :
    Rest (n := 1617) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 1603), (1, 1553), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1609), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]
      13 0x105090 bytes_l10446f_41 b_l10446f_41 := by
  have f820 : InstrSpec 0x105090 [0xF7, 0xD1] (fun s => s.RIP = 0x105090) (notR32Effect 0x105090 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR32Effect_footprint 0x105090 2 1).toInstrSpec (not_r32_effect_step 0x105090 0xd1 (by decide) (by decide)) pre_rip
  have f821 : InstrSpec 0x105092 [0x66, 0x89, 0x8C, 0x24, 0xA2, 0x00, 0x00, 0x00] (StorePre 0x105092 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x105092 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x105092 8 1 (.sib 4 none 0 (.d32 0xa2)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105092 8 1 (.sib 4 none 0 (.d32 0xa2))).toInstrSpec (mov_m16_r16_effect_step 0x105092 1 (.sib 4 none 0 (.d32 0xa2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f822 : InstrSpec 0x10509a [0xF7, 0xD6] (fun s => s.RIP = 0x10509a) (notR32Effect 0x10509a 2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR32Effect_footprint 0x10509a 2 6).toInstrSpec (not_r32_effect_step 0x10509a 0xd6 (by decide) (by decide)) pre_rip
  have f823 : InstrSpec 0x10509c [0x66, 0x89, 0xB4, 0x24, 0xA4, 0x00, 0x00, 0x00] (StorePre 0x10509c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x10509c + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10509c 8 6 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10509c 8 6 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (mov_m16_r16_effect_step 0x10509c 6 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f824 : InstrSpec 0x1050a4 [0x66, 0xF7, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x1050a4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1050a4 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1050a4 8 16 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1050a4 8 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (not_m16_effect_step 0x1050a4 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f825 : InstrSpec 0x1050ac [0x66, 0xF7, 0x94, 0x24, 0xAA, 0x00, 0x00, 0x00] (StorePre 0x1050ac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaa)) s (0x1050ac + BitVec.ofNat 64 8)) 2) (notMEffect 0x1050ac 8 16 (.sib 4 none 0 (.d32 0xaa)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1050ac 8 (.sib 4 none 0 (.d32 0xaa))).toInstrSpec (not_m16_effect_step 0x1050ac (.sib 4 none 0 (.d32 0xaa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f826 : InstrSpec 0x1050b4 [0x66, 0xF7, 0x94, 0x24, 0xB2, 0x00, 0x00, 0x00] (StorePre 0x1050b4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb2)) s (0x1050b4 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1050b4 8 16 (.sib 4 none 0 (.d32 0xb2)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1050b4 8 (.sib 4 none 0 (.d32 0xb2))).toInstrSpec (not_m16_effect_step 0x1050b4 (.sib 4 none 0 (.d32 0xb2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f827 : InstrSpec 0x1050bc [0x66, 0xF7, 0x94, 0x24, 0xB4, 0x00, 0x00, 0x00] (StorePre 0x1050bc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x1050bc + BitVec.ofNat 64 8)) 2) (notMEffect 0x1050bc 8 16 (.sib 4 none 0 (.d32 0xb4)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x1050bc 8 (.sib 4 none 0 (.d32 0xb4))).toInstrSpec (not_m16_effect_step 0x1050bc (.sib 4 none 0 (.d32 0xb4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f828 : InstrSpec 0x1050c4 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x1050c4) (leaR64Effect 0x1050c4 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1050c4 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1050c4 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f829 : InstrSpec 0x1050c9 [0xBA, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1050c9) (movR32Imm32Effect 0x1050c9 5 2 0xb0)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1050c9 5 2 0xb0).toInstrSpec (mov_r32_imm32_effect_step 0x1050c9 0xba (by decide) 0xb0) pre_rip
  have f830 : InstrSpec 0x1050ce [0x48, 0x8B, 0x9C, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x1050ce (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1050ce + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1050ce 3 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1050ce 3 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x1050ce 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f831 : InstrSpec 0x1050d6 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1050d6) (movR64R64Effect 0x1050d6 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1050d6 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1050d6 0x48 0xdf (by decide) (by decide)) pre_rip
  have f832 : InstrSpec 0x1050d9 [0xFF, 0x15, 0x29, 0xC1, 0x0F, 0x00] (GoesTo (CallMemPre 0x1050d9 (.rip 0xfc129)) (callEffect (callMemPtr 0x1050d9 (.rip 0xfc129)) (0x1050d9 + BitVec.ofNat 64 (callMemLen (.rip 0xfc129)))) 0x103f00) (callEffect (callMemPtr 0x1050d9 (.rip 0xfc129)) (0x1050d9 + BitVec.ofNat 64 (callMemLen (.rip 0xfc129))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x1050d9 (.rip 0xfc129)).toInstrSpec (call_m64_effect_step 0x1050d9 (.rip 0xfc129) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 1617) (RestInside.out (n := 1617) f820 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1618) (ρ' := [(0, 1603), (1, 1617), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1609), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105092) f820 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1619) (RestInside.exec (n := 1619) (ρ' := [(0, 1603), (1, 1617), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1609), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10509a) f821 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1620) (RestInside.out (n := 1620) f822 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1621) (ρ' := [(0, 1603), (1, 1617), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1620), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10509c) f822 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1622) (RestInside.exec (n := 1622) (ρ' := [(0, 1603), (1, 1617), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1620), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050a4) f823 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1623) (RestInside.exec (n := 1623) (ρ' := [(0, 1603), (1, 1617), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1620), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050ac) f824 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1624) (RestInside.exec (n := 1624) (ρ' := [(0, 1603), (1, 1617), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1620), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050b4) f825 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1625) (RestInside.exec (n := 1625) (ρ' := [(0, 1603), (1, 1617), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1620), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050bc) f826 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1626) (RestInside.exec (n := 1626) (ρ' := [(0, 1603), (1, 1617), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1620), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050c4) f827 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1627) (RestInside.out (n := 1627) f828 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1628) (ρ' := [(0, 1603), (1, 1617), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1627), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050c9) f828 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1629) (RestInside.out (n := 1629) f829 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1630) (ρ' := [(0, 1603), (1, 1617), (2, 1629), (3, 1566), (4, 4), (5, 1581), (6, 1627), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050ce) f829 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1631) (RestInside.out (n := 1631) f830 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1632) (ρ' := [(0, 1603), (1, 1617), (2, 1629), (3, 1631), (4, 4), (5, 1581), (6, 1627), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050d6) f830 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1633) (RestInside.out (n := 1633) f831 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1634) (ρ' := [(0, 1603), (1, 1617), (2, 1629), (3, 1631), (4, 4), (5, 1581), (6, 1627), (7, 1633), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050d9) f831 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1635) (RestInside.out (n := 1635) f832 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1636) (ρ' := [(0, 1603), (1, 1617), (2, 1629), (3, 1631), (4, 1635), (5, 1581), (6, 1627), (7, 1633), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f832 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 1637) (by decide) (by decide) rfl rfl

theorem rest_l10446f_40 [Bindings] (code : CodeMap) :
    Rest (n := 1587) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      33 0x10502a bytes_l10446f_40 b_l10446f_40 := by
  have f800 : InstrSpec 0x10502a [0x41, 0xF7, 0xD7] (fun s => s.RIP = 0x10502a) (notR32Effect 0x10502a 3 15)
      [.gpr 15] [] [.reg 15, .rip] :=
    (notR32Effect_footprint 0x10502a 3 15).toInstrSpec (not_r32_rex_effect_step 0x10502a 0x41 0xd7 (by decide) (by decide) (by decide)) pre_rip
  have f801 : InstrSpec 0x10502d [0x66, 0x44, 0x89, 0x7C, 0x24, 0x78] (StorePre 0x10502d 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10502d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x10502d 6 15 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10502d 6 15 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m16_r16_rex_effect_step 0x10502d 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f802 : InstrSpec 0x105033 [0x66, 0xF7, 0x54, 0x24, 0x7A] (StorePre 0x105033 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7a)) s (0x105033 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105033 5 16 (.sib 4 none 0 (.d8 0x7a)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x105033 5 (.sib 4 none 0 (.d8 0x7a))).toInstrSpec (not_m16_effect_step 0x105033 (.sib 4 none 0 (.d8 0x7a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f803 : InstrSpec 0x105038 [0x89, 0xC6] (fun s => s.RIP = 0x105038) (movR32R32Effect 0x105038 2 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x105038 2 6 0).toInstrSpec (mov_r32_r32_effect_step 0x105038 0xc6 (by decide)) pre_rip
  have f804 : InstrSpec 0x10503a [0x66, 0xF7, 0x94, 0x24, 0x82, 0x00, 0x00, 0x00] (StorePre 0x10503a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x10503a + BitVec.ofNat 64 8)) 2) (notMEffect 0x10503a 8 16 (.sib 4 none 0 (.d32 0x82)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x10503a 8 (.sib 4 none 0 (.d32 0x82))).toInstrSpec (not_m16_effect_step 0x10503a (.sib 4 none 0 (.d32 0x82)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f805 : InstrSpec 0x105042 [0xD1, 0xEE] (fun s => s.RIP = 0x105042) (shrR32Effect 0x105042 2 6 1)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x105042 2 6 1).toInstrSpec (shr_r32_one_effect_step 0x105042 0xee (by decide) (by decide)) pre_rip
  have f806 : InstrSpec 0x105044 [0x66, 0xF7, 0x94, 0x24, 0x84, 0x00, 0x00, 0x00] (StorePre 0x105044 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x105044 + BitVec.ofNat 64 8)) 2) (notMEffect 0x105044 8 16 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x105044 8 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (not_m16_effect_step 0x105044 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f807 : InstrSpec 0x10504c [0x31, 0xC6] (fun s => s.RIP = 0x10504c) (xorR32R32Effect 0x10504c 2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10504c 2 6 0).toInstrSpec (xor_r32_r32_effect_step 0x10504c 0xc6 (by decide)) pre_rip
  have f808 : InstrSpec 0x10504e [0x66, 0xF7, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (StorePre 0x10504e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10504e + BitVec.ofNat 64 8)) 2) (notMEffect 0x10504e 8 16 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x10504e 8 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (not_m16_effect_step 0x10504e (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f809 : InstrSpec 0x105056 [0x81, 0xE6, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x105056) (andR32Imm32Effect 0x105056 6 6 0x5050)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105056 6 6 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x105056 0xe6 0x5050 (by decide) (by decide)) pre_rip
  have f810 : InstrSpec 0x10505c [0x66, 0xF7, 0x94, 0x24, 0x8A, 0x00, 0x00, 0x00] (StorePre 0x10505c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8a)) s (0x10505c + BitVec.ofNat 64 8)) 2) (notMEffect 0x10505c 8 16 (.sib 4 none 0 (.d32 0x8a)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x10505c 8 (.sib 4 none 0 (.d32 0x8a))).toInstrSpec (not_m16_effect_step 0x10505c (.sib 4 none 0 (.d32 0x8a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f811 : InstrSpec 0x105064 [0x31, 0xF0] (fun s => s.RIP = 0x105064) (xorR32R32Effect 0x105064 2 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105064 2 0 6).toInstrSpec (xor_r32_r32_effect_step 0x105064 0xf0 (by decide)) pre_rip
  have f812 : InstrSpec 0x105066 [0x66, 0xF7, 0x94, 0x24, 0x92, 0x00, 0x00, 0x00] (StorePre 0x105066 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x92)) s (0x105066 + BitVec.ofNat 64 8)) 2) (notMEffect 0x105066 8 16 (.sib 4 none 0 (.d32 0x92)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x105066 8 (.sib 4 none 0 (.d32 0x92))).toInstrSpec (not_m16_effect_step 0x105066 (.sib 4 none 0 (.d32 0x92)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f813 : InstrSpec 0x10506e [0x01, 0xF6] (fun s => s.RIP = 0x10506e) (addR32R32Effect 0x10506e 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10506e 2 6 6).toInstrSpec (add_r32_r32_effect_step 0x10506e 0xf6 (by decide)) pre_rip
  have f814 : InstrSpec 0x105070 [0x66, 0xF7, 0x94, 0x24, 0x94, 0x00, 0x00, 0x00] (StorePre 0x105070 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x94)) s (0x105070 + BitVec.ofNat 64 8)) 2) (notMEffect 0x105070 8 16 (.sib 4 none 0 (.d32 0x94)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x105070 8 (.sib 4 none 0 (.d32 0x94))).toInstrSpec (not_m16_effect_step 0x105070 (.sib 4 none 0 (.d32 0x94)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f815 : InstrSpec 0x105078 [0x31, 0xC6] (fun s => s.RIP = 0x105078) (xorR32R32Effect 0x105078 2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105078 2 6 0).toInstrSpec (xor_r32_r32_effect_step 0x105078 0xc6 (by decide)) pre_rip
  have f816 : InstrSpec 0x10507a [0x41, 0xF7, 0xD4] (fun s => s.RIP = 0x10507a) (notR32Effect 0x10507a 3 12)
      [.gpr 12] [] [.reg 12, .rip] :=
    (notR32Effect_footprint 0x10507a 3 12).toInstrSpec (not_r32_rex_effect_step 0x10507a 0x41 0xd4 (by decide) (by decide) (by decide)) pre_rip
  have f817 : InstrSpec 0x10507d [0x66, 0x44, 0x89, 0xA4, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x10507d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10507d + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x10507d 9 12 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10507d 9 12 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m16_r16_rex_effect_step 0x10507d 0x44 (by decide) 4 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f818 : InstrSpec 0x105086 [0xF7, 0xD2] (fun s => s.RIP = 0x105086) (notR32Effect 0x105086 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (notR32Effect_footprint 0x105086 2 2).toInstrSpec (not_r32_effect_step 0x105086 0xd2 (by decide) (by decide)) pre_rip
  have f819 : InstrSpec 0x105088 [0x66, 0x89, 0x94, 0x24, 0x9A, 0x00, 0x00, 0x00] (StorePre 0x105088 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9a)) s (0x105088 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x105088 8 2 (.sib 4 none 0 (.d32 0x9a)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105088 8 2 (.sib 4 none 0 (.d32 0x9a))).toInstrSpec (mov_m16_r16_effect_step 0x105088 2 (.sib 4 none 0 (.d32 0x9a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 1587) (RestInside.out (n := 1587) f800 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1588) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10502d) f800 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1589) (RestInside.exec (n := 1589) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105033) f801 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1590) (RestInside.exec (n := 1590) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105038) f802 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1591) (RestInside.out (n := 1591) f803 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1592) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1591), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10503a) f803 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1593) (RestInside.exec (n := 1593) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1591), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105042) f804 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1594) (RestInside.out (n := 1594) f805 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1595) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1594), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105044) f805 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1596) (RestInside.exec (n := 1596) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1594), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10504c) f806 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1597) (RestInside.out (n := 1597) f807 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1598) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1597), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10504e) f807 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1599) (RestInside.exec (n := 1599) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1597), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105056) f808 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1600) (RestInside.out (n := 1600) f809 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1601) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1600), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10505c) f809 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1602) (RestInside.exec (n := 1602) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1600), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105064) f810 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1603) (RestInside.out (n := 1603) f811 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1604) (ρ' := [(0, 1603), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1600), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105066) f811 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1605) (RestInside.exec (n := 1605) (ρ' := [(0, 1603), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1600), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10506e) f812 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1606) (RestInside.out (n := 1606) f813 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1607) (ρ' := [(0, 1603), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1606), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105070) f813 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1608) (RestInside.exec (n := 1608) (ρ' := [(0, 1603), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1606), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105078) f814 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1609) (RestInside.out (n := 1609) f815 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1610) (ρ' := [(0, 1603), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1609), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10507a) f815 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1611) (RestInside.out (n := 1611) f816 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1612) (ρ' := [(0, 1603), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1609), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10507d) f816 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1613) (RestInside.exec (n := 1613) (ρ' := [(0, 1603), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1609), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105086) f817 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1614) (RestInside.out (n := 1614) f818 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1615) (ρ' := [(0, 1603), (1, 1553), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1609), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105088) f818 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1616) (RestInside.exec (n := 1616) (ρ' := [(0, 1603), (1, 1553), (2, 1614), (3, 1566), (4, 4), (5, 1581), (6, 1609), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1611), (13, 1519), (14, 1584), (15, 1587), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105090) f819 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10446f_41 code

theorem rest_l10446f_39 [Bindings] (code : CodeMap) :
    Rest (n := 1555) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 1547), (1, 1553), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      53 0x104fdd bytes_l10446f_39 b_l10446f_39 := by
  have f780 : InstrSpec 0x104fdd [0x41, 0xF7, 0xD1] (fun s => s.RIP = 0x104fdd) (notR32Effect 0x104fdd 3 9)
      [.gpr 9] [] [.reg 9, .rip] :=
    (notR32Effect_footprint 0x104fdd 3 9).toInstrSpec (not_r32_rex_effect_step 0x104fdd 0x41 0xd1 (by decide) (by decide) (by decide)) pre_rip
  have f781 : InstrSpec 0x104fe0 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x58] (StorePre 0x104fe0 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x104fe0 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104fe0 6 9 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104fe0 6 9 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104fe0 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f782 : InstrSpec 0x104fe6 [0x89, 0xD8] (fun s => s.RIP = 0x104fe6) (movR32R32Effect 0x104fe6 2 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x104fe6 2 0 3).toInstrSpec (mov_r32_r32_effect_step 0x104fe6 0xd8 (by decide)) pre_rip
  have f783 : InstrSpec 0x104fe8 [0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x104fe8) (shrR32Effect 0x104fe8 3 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x104fe8 3 0 2).toInstrSpec (shr_r32_imm8_effect_step 0x104fe8 0xe8 0x2 (by decide) (by decide)) pre_rip
  have f784 : InstrSpec 0x104feb [0x31, 0xD8] (fun s => s.RIP = 0x104feb) (xorR32R32Effect 0x104feb 2 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104feb 2 0 3).toInstrSpec (xor_r32_r32_effect_step 0x104feb 0xd8 (by decide)) pre_rip
  have f785 : InstrSpec 0x104fed [0x25, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104fed) (andEaxImm32Effect 0x104fed 0x1320)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x104fed 0x1320).toInstrSpec (and_eax_imm32_effect_step 0x104fed 0x1320) pre_rip
  have f786 : InstrSpec 0x104ff2 [0x31, 0xC3] (fun s => s.RIP = 0x104ff2) (xorR32R32Effect 0x104ff2 2 3 0)
      [.gpr 3, .gpr 0] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ff2 2 3 0).toInstrSpec (xor_r32_r32_effect_step 0x104ff2 0xc3 (by decide)) pre_rip
  have f787 : InstrSpec 0x104ff4 [0xC1, 0xE0, 0x02] (fun s => s.RIP = 0x104ff4) (shlR32Effect 0x104ff4 3 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x104ff4 3 0 2).toInstrSpec (shl_r32_imm8_effect_step 0x104ff4 0xe0 0x2 (by decide) (by decide)) pre_rip
  have f788 : InstrSpec 0x104ff7 [0x66, 0xF7, 0x54, 0x24, 0x5A] (StorePre 0x104ff7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x104ff7 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104ff7 5 16 (.sib 4 none 0 (.d8 0x5a)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104ff7 5 (.sib 4 none 0 (.d8 0x5a))).toInstrSpec (not_m16_effect_step 0x104ff7 (.sib 4 none 0 (.d8 0x5a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f789 : InstrSpec 0x104ffc [0x31, 0xD8] (fun s => s.RIP = 0x104ffc) (xorR32R32Effect 0x104ffc 2 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ffc 2 0 3).toInstrSpec (xor_r32_r32_effect_step 0x104ffc 0xd8 (by decide)) pre_rip
  have f790 : InstrSpec 0x104ffe [0x66, 0xF7, 0x54, 0x24, 0x62] (StorePre 0x104ffe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x104ffe + BitVec.ofNat 64 5)) 2) (notMEffect 0x104ffe 5 16 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104ffe 5 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (not_m16_effect_step 0x104ffe (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f791 : InstrSpec 0x105003 [0x66, 0xF7, 0x54, 0x24, 0x64] (StorePre 0x105003 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x105003 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105003 5 16 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x105003 5 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (not_m16_effect_step 0x105003 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f792 : InstrSpec 0x105008 [0x41, 0xF7, 0xD2] (fun s => s.RIP = 0x105008) (notR32Effect 0x105008 3 10)
      [.gpr 10] [] [.reg 10, .rip] :=
    (notR32Effect_footprint 0x105008 3 10).toInstrSpec (not_r32_rex_effect_step 0x105008 0x41 0xd2 (by decide) (by decide) (by decide)) pre_rip
  have f793 : InstrSpec 0x10500b [0x66, 0x44, 0x89, 0x54, 0x24, 0x68] (StorePre 0x10500b 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10500b + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x10500b 6 10 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10500b 6 10 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m16_r16_rex_effect_step 0x10500b 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f794 : InstrSpec 0x105011 [0x41, 0xF7, 0xD3] (fun s => s.RIP = 0x105011) (notR32Effect 0x105011 3 11)
      [.gpr 11] [] [.reg 11, .rip] :=
    (notR32Effect_footprint 0x105011 3 11).toInstrSpec (not_r32_rex_effect_step 0x105011 0x41 0xd3 (by decide) (by decide) (by decide)) pre_rip
  have f795 : InstrSpec 0x105014 [0x66, 0x44, 0x89, 0x5C, 0x24, 0x6A] (StorePre 0x105014 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x105014 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x105014 6 11 (.sib 4 none 0 (.d8 0x6a)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105014 6 11 (.sib 4 none 0 (.d8 0x6a))).toInstrSpec (mov_m16_r16_rex_effect_step 0x105014 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x6a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f796 : InstrSpec 0x10501a [0xF7, 0xD5] (fun s => s.RIP = 0x10501a) (notR32Effect 0x10501a 2 5)
      [.gpr 5] [] [.reg 5, .rip] :=
    (notR32Effect_footprint 0x10501a 2 5).toInstrSpec (not_r32_effect_step 0x10501a 0xd5 (by decide) (by decide)) pre_rip
  have f797 : InstrSpec 0x10501c [0x66, 0x89, 0x6C, 0x24, 0x72] (StorePre 0x10501c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x10501c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10501c 5 5 (.sib 4 none 0 (.d8 0x72)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10501c 5 5 (.sib 4 none 0 (.d8 0x72))).toInstrSpec (mov_m16_r16_effect_step 0x10501c 5 (.sib 4 none 0 (.d8 0x72)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f798 : InstrSpec 0x105021 [0x41, 0xF7, 0xD6] (fun s => s.RIP = 0x105021) (notR32Effect 0x105021 3 14)
      [.gpr 14] [] [.reg 14, .rip] :=
    (notR32Effect_footprint 0x105021 3 14).toInstrSpec (not_r32_rex_effect_step 0x105021 0x41 0xd6 (by decide) (by decide) (by decide)) pre_rip
  have f799 : InstrSpec 0x105024 [0x66, 0x44, 0x89, 0x74, 0x24, 0x74] (StorePre 0x105024 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x105024 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x105024 6 14 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105024 6 14 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (mov_m16_r16_rex_effect_step 0x105024 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 1555) (RestInside.out (n := 1555) f780 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1556) (ρ' := [(0, 1547), (1, 1553), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fe0) f780 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1557) (RestInside.exec (n := 1557) (ρ' := [(0, 1547), (1, 1553), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fe6) f781 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1558) (RestInside.out (n := 1558) f782 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1559) (ρ' := [(0, 1558), (1, 1553), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fe8) f782 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1560) (RestInside.out (n := 1560) f783 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1561) (ρ' := [(0, 1560), (1, 1553), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104feb) f783 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1562) (RestInside.out (n := 1562) f784 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1563) (ρ' := [(0, 1562), (1, 1553), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fed) f784 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1564) (RestInside.out (n := 1564) f785 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1565) (ρ' := [(0, 1564), (1, 1553), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ff2) f785 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1566) (RestInside.out (n := 1566) f786 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1567) (ρ' := [(0, 1564), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ff4) f786 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1568) (RestInside.out (n := 1568) f787 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1569) (ρ' := [(0, 1568), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ff7) f787 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1570) (RestInside.exec (n := 1570) (ρ' := [(0, 1568), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ffc) f788 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1571) (RestInside.out (n := 1571) f789 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1572) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ffe) f789 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1573) (RestInside.exec (n := 1573) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105003) f790 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1574) (RestInside.exec (n := 1574) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105008) f791 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1575) (RestInside.out (n := 1575) f792 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1576) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10500b) f792 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1577) (RestInside.exec (n := 1577) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105011) f793 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1578) (RestInside.out (n := 1578) f794 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1579) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105014) f794 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1580) (RestInside.exec (n := 1580) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10501a) f795 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1581) (RestInside.out (n := 1581) f796 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1582) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10501c) f796 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1583) (RestInside.exec (n := 1583) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105021) f797 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1584) (RestInside.out (n := 1584) f798 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1585) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105024) f798 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1586) (RestInside.exec (n := 1586) (ρ' := [(0, 1571), (1, 1553), (2, 1365), (3, 1566), (4, 4), (5, 1581), (6, 1525), (7, 1528), (8, 1531), (9, 1555), (10, 1575), (11, 1578), (12, 1335), (13, 1519), (14, 1584), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10502a) f799 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10446f_40 code

theorem rest_l10446f_38 [Bindings] (code : CodeMap) :
    Rest (n := 1525) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 1513), (1, 1522), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      73 0x104f91 bytes_l10446f_38 b_l10446f_38 := by
  have f760 : InstrSpec 0x104f91 [0xF7, 0xD6] (fun s => s.RIP = 0x104f91) (notR32Effect 0x104f91 2 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (notR32Effect_footprint 0x104f91 2 6).toInstrSpec (not_r32_effect_step 0x104f91 0xd6 (by decide) (by decide)) pre_rip
  have f761 : InstrSpec 0x104f93 [0x66, 0x89, 0x74, 0x24, 0x32] (StorePre 0x104f93 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x104f93 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104f93 5 6 (.sib 4 none 0 (.d8 0x32)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104f93 5 6 (.sib 4 none 0 (.d8 0x32))).toInstrSpec (mov_m16_r16_effect_step 0x104f93 6 (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f762 : InstrSpec 0x104f98 [0xF7, 0xD7] (fun s => s.RIP = 0x104f98) (notR32Effect 0x104f98 2 7)
      [.gpr 7] [] [.reg 7, .rip] :=
    (notR32Effect_footprint 0x104f98 2 7).toInstrSpec (not_r32_effect_step 0x104f98 0xd7 (by decide) (by decide)) pre_rip
  have f763 : InstrSpec 0x104f9a [0x66, 0x89, 0x7C, 0x24, 0x34] (StorePre 0x104f9a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x104f9a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104f9a 5 7 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104f9a 5 7 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_m16_r16_effect_step 0x104f9a 7 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f764 : InstrSpec 0x104f9f [0x41, 0xF7, 0xD0] (fun s => s.RIP = 0x104f9f) (notR32Effect 0x104f9f 3 8)
      [.gpr 8] [] [.reg 8, .rip] :=
    (notR32Effect_footprint 0x104f9f 3 8).toInstrSpec (not_r32_rex_effect_step 0x104f9f 0x41 0xd0 (by decide) (by decide) (by decide)) pre_rip
  have f765 : InstrSpec 0x104fa2 [0x66, 0x44, 0x89, 0x44, 0x24, 0x38] (StorePre 0x104fa2 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x104fa2 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104fa2 6 8 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104fa2 6 8 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104fa2 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f766 : InstrSpec 0x104fa8 [0x66, 0xF7, 0x54, 0x24, 0x3A] (StorePre 0x104fa8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x104fa8 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fa8 5 16 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104fa8 5 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (not_m16_effect_step 0x104fa8 (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f767 : InstrSpec 0x104fad [0x89, 0xC1] (fun s => s.RIP = 0x104fad) (movR32R32Effect 0x104fad 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x104fad 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x104fad 0xc1 (by decide)) pre_rip
  have f768 : InstrSpec 0x104faf [0x66, 0xF7, 0x54, 0x24, 0x42] (StorePre 0x104faf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x104faf + BitVec.ofNat 64 5)) 2) (notMEffect 0x104faf 5 16 (.sib 4 none 0 (.d8 0x42)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104faf 5 (.sib 4 none 0 (.d8 0x42))).toInstrSpec (not_m16_effect_step 0x104faf (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f769 : InstrSpec 0x104fb4 [0xD1, 0xE9] (fun s => s.RIP = 0x104fb4) (shrR32Effect 0x104fb4 2 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x104fb4 2 1 1).toInstrSpec (shr_r32_one_effect_step 0x104fb4 0xe9 (by decide) (by decide)) pre_rip
  have f770 : InstrSpec 0x104fb6 [0x66, 0xF7, 0x54, 0x24, 0x44] (StorePre 0x104fb6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x104fb6 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fb6 5 16 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104fb6 5 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (not_m16_effect_step 0x104fb6 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f771 : InstrSpec 0x104fbb [0x31, 0xC1] (fun s => s.RIP = 0x104fbb) (xorR32R32Effect 0x104fbb 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104fbb 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x104fbb 0xc1 (by decide)) pre_rip
  have f772 : InstrSpec 0x104fbd [0x66, 0xF7, 0x54, 0x24, 0x48] (StorePre 0x104fbd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x104fbd + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fbd 5 16 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104fbd 5 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (not_m16_effect_step 0x104fbd (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f773 : InstrSpec 0x104fc2 [0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104fc2) (andR32Imm32Effect 0x104fc2 6 1 0x5050)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104fc2 6 1 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104fc2 0xe1 0x5050 (by decide) (by decide)) pre_rip
  have f774 : InstrSpec 0x104fc8 [0x66, 0xF7, 0x54, 0x24, 0x4A] (StorePre 0x104fc8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x104fc8 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fc8 5 16 (.sib 4 none 0 (.d8 0x4a)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104fc8 5 (.sib 4 none 0 (.d8 0x4a))).toInstrSpec (not_m16_effect_step 0x104fc8 (.sib 4 none 0 (.d8 0x4a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f775 : InstrSpec 0x104fcd [0x31, 0xC8] (fun s => s.RIP = 0x104fcd) (xorR32R32Effect 0x104fcd 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104fcd 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x104fcd 0xc8 (by decide)) pre_rip
  have f776 : InstrSpec 0x104fcf [0x66, 0xF7, 0x54, 0x24, 0x52] (StorePre 0x104fcf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x52)) s (0x104fcf + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fcf 5 16 (.sib 4 none 0 (.d8 0x52)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104fcf 5 (.sib 4 none 0 (.d8 0x52))).toInstrSpec (not_m16_effect_step 0x104fcf (.sib 4 none 0 (.d8 0x52)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f777 : InstrSpec 0x104fd4 [0x01, 0xC9] (fun s => s.RIP = 0x104fd4) (addR32R32Effect 0x104fd4 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104fd4 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x104fd4 0xc9 (by decide)) pre_rip
  have f778 : InstrSpec 0x104fd6 [0x66, 0xF7, 0x54, 0x24, 0x54] (StorePre 0x104fd6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x104fd6 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104fd6 5 16 (.sib 4 none 0 (.d8 0x54)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104fd6 5 (.sib 4 none 0 (.d8 0x54))).toInstrSpec (not_m16_effect_step 0x104fd6 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f779 : InstrSpec 0x104fdb [0x31, 0xC1] (fun s => s.RIP = 0x104fdb) (xorR32R32Effect 0x104fdb 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104fdb 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x104fdb 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 1525) (RestInside.out (n := 1525) f760 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1526) (ρ' := [(0, 1513), (1, 1522), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f93) f760 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1527) (RestInside.exec (n := 1527) (ρ' := [(0, 1513), (1, 1522), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f98) f761 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1528) (RestInside.out (n := 1528) f762 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1529) (ρ' := [(0, 1513), (1, 1522), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f9a) f762 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1530) (RestInside.exec (n := 1530) (ρ' := [(0, 1513), (1, 1522), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f9f) f763 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1531) (RestInside.out (n := 1531) f764 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1532) (ρ' := [(0, 1513), (1, 1522), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fa2) f764 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1533) (RestInside.exec (n := 1533) (ρ' := [(0, 1513), (1, 1522), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fa8) f765 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1534) (RestInside.exec (n := 1534) (ρ' := [(0, 1513), (1, 1522), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fad) f766 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1535) (RestInside.out (n := 1535) f767 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1536) (ρ' := [(0, 1513), (1, 1535), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104faf) f767 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1537) (RestInside.exec (n := 1537) (ρ' := [(0, 1513), (1, 1535), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fb4) f768 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1538) (RestInside.out (n := 1538) f769 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1539) (ρ' := [(0, 1513), (1, 1538), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fb6) f769 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1540) (RestInside.exec (n := 1540) (ρ' := [(0, 1513), (1, 1538), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fbb) f770 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1541) (RestInside.out (n := 1541) f771 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1542) (ρ' := [(0, 1513), (1, 1541), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fbd) f771 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1543) (RestInside.exec (n := 1543) (ρ' := [(0, 1513), (1, 1541), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fc2) f772 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1544) (RestInside.out (n := 1544) f773 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1545) (ρ' := [(0, 1513), (1, 1544), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fc8) f773 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1546) (RestInside.exec (n := 1546) (ρ' := [(0, 1513), (1, 1544), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fcd) f774 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1547) (RestInside.out (n := 1547) f775 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1548) (ρ' := [(0, 1547), (1, 1544), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fcf) f775 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1549) (RestInside.exec (n := 1549) (ρ' := [(0, 1547), (1, 1544), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fd4) f776 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1550) (RestInside.out (n := 1550) f777 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1551) (ρ' := [(0, 1547), (1, 1550), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fd6) f777 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1552) (RestInside.exec (n := 1552) (ρ' := [(0, 1547), (1, 1550), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fdb) f778 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1553) (RestInside.out (n := 1553) f779 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1554) (ρ' := [(0, 1547), (1, 1553), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 1525), (7, 1528), (8, 1531), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104fdd) f779 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_39 code

theorem rest_l10446f_37 [Bindings] (code : CodeMap) :
    Rest (n := 1492) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 1488), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      93 0x104f35 bytes_l10446f_37 b_l10446f_37 := by
  have f740 : InstrSpec 0x104f35 [0x0F, 0xB7, 0x9C, 0x24, 0xA4, 0x00, 0x00, 0x00] (LoadPre 0x104f35 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x104f35 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104f35 8 3 (.sib 4 none 0 (.d32 0xa4)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104f35 8 3 (.sib 4 none 0 (.d32 0xa4))).toInstrSpec (movzx_r32_m16_effect_step 0x104f35 3 (.sib 4 none 0 (.d32 0xa4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f741 : InstrSpec 0x104f3d [0x66, 0x89, 0x84, 0x24, 0xA6, 0x00, 0x00, 0x00] (StorePre 0x104f3d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x104f3d + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104f3d 8 0 (.sib 4 none 0 (.d32 0xa6)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104f3d 8 0 (.sib 4 none 0 (.d32 0xa6))).toInstrSpec (mov_m16_r16_effect_step 0x104f3d 0 (.sib 4 none 0 (.d32 0xa6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f742 : InstrSpec 0x104f45 [0x8B, 0x84, 0x24, 0xBC, 0x00, 0x00, 0x00] (LoadPre 0x104f45 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x104f45 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x104f45 0 (.sib 4 none 0 (.d32 0xbc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x104f45 0 (.sib 4 none 0 (.d32 0xbc))).toInstrSpec (mov_r32_m32_low_effect_step 0x104f45 0 (.sib 4 none 0 (.d32 0xbc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f743 : InstrSpec 0x104f4c [0xF7, 0xD0] (fun s => s.RIP = 0x104f4c) (notR32Effect 0x104f4c 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x104f4c 2 0).toInstrSpec (not_r32_effect_step 0x104f4c 0xd0 (by decide) (by decide)) pre_rip
  have f744 : InstrSpec 0x104f4e [0x66, 0x89, 0x44, 0x24, 0x18] (StorePre 0x104f4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x104f4e + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104f4e 5 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104f4e 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m16_r16_effect_step 0x104f4e 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f745 : InstrSpec 0x104f53 [0x44, 0x89, 0xE8] (fun s => s.RIP = 0x104f53) (movR32R32Effect 0x104f53 3 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x104f53 3 0 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x104f53 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f746 : InstrSpec 0x104f56 [0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x104f56) (shrR32Effect 0x104f56 3 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x104f56 3 0 2).toInstrSpec (shr_r32_imm8_effect_step 0x104f56 0xe8 0x2 (by decide) (by decide)) pre_rip
  have f747 : InstrSpec 0x104f59 [0x44, 0x31, 0xE8] (fun s => s.RIP = 0x104f59) (xorR32R32Effect 0x104f59 3 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104f59 3 0 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104f59 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f748 : InstrSpec 0x104f5c [0x25, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104f5c) (andEaxImm32Effect 0x104f5c 0x1320)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x104f5c 0x1320).toInstrSpec (and_eax_imm32_effect_step 0x104f5c 0x1320) pre_rip
  have f749 : InstrSpec 0x104f61 [0x41, 0x31, 0xC5] (fun s => s.RIP = 0x104f61) (xorR32R32Effect 0x104f61 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104f61 3 13 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x104f61 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f750 : InstrSpec 0x104f64 [0xC1, 0xE0, 0x02] (fun s => s.RIP = 0x104f64) (shlR32Effect 0x104f64 3 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x104f64 3 0 2).toInstrSpec (shl_r32_imm8_effect_step 0x104f64 0xe0 0x2 (by decide) (by decide)) pre_rip
  have f751 : InstrSpec 0x104f67 [0x66, 0xF7, 0x54, 0x24, 0x1A] (StorePre 0x104f67 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x104f67 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104f67 5 16 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104f67 5 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (not_m16_effect_step 0x104f67 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f752 : InstrSpec 0x104f6c [0x44, 0x31, 0xE8] (fun s => s.RIP = 0x104f6c) (xorR32R32Effect 0x104f6c 3 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104f6c 3 0 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104f6c 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f753 : InstrSpec 0x104f6f [0x66, 0xF7, 0x54, 0x24, 0x22] (StorePre 0x104f6f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x104f6f + BitVec.ofNat 64 5)) 2) (notMEffect 0x104f6f 5 16 (.sib 4 none 0 (.d8 0x22)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104f6f 5 (.sib 4 none 0 (.d8 0x22))).toInstrSpec (not_m16_effect_step 0x104f6f (.sib 4 none 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f754 : InstrSpec 0x104f74 [0x66, 0xF7, 0x54, 0x24, 0x24] (StorePre 0x104f74 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x104f74 + BitVec.ofNat 64 5)) 2) (notMEffect 0x104f74 5 16 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.rip] :=
    (notMEffect16_footprint 0x104f74 5 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (not_m16_effect_step 0x104f74 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f755 : InstrSpec 0x104f79 [0x44, 0x8B, 0xAC, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x104f79 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x104f79 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x104f79 13 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x104f79 13 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r32_m32_effect_step 0x104f79 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f756 : InstrSpec 0x104f81 [0x41, 0xF7, 0xD5] (fun s => s.RIP = 0x104f81) (notR32Effect 0x104f81 3 13)
      [.gpr 13] [] [.reg 13, .rip] :=
    (notR32Effect_footprint 0x104f81 3 13).toInstrSpec (not_r32_rex_effect_step 0x104f81 0x41 0xd5 (by decide) (by decide) (by decide)) pre_rip
  have f757 : InstrSpec 0x104f84 [0x66, 0x44, 0x89, 0x6C, 0x24, 0x28] (StorePre 0x104f84 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x104f84 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104f84 6 13 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104f84 6 13 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104f84 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f758 : InstrSpec 0x104f8a [0xF7, 0xD1] (fun s => s.RIP = 0x104f8a) (notR32Effect 0x104f8a 2 1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (notR32Effect_footprint 0x104f8a 2 1).toInstrSpec (not_r32_effect_step 0x104f8a 0xd1 (by decide) (by decide)) pre_rip
  have f759 : InstrSpec 0x104f8c [0x66, 0x89, 0x4C, 0x24, 0x2A] (StorePre 0x104f8c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x104f8c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104f8c 5 1 (.sib 4 none 0 (.d8 0x2a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104f8c 5 1 (.sib 4 none 0 (.d8 0x2a))).toInstrSpec (mov_m16_r16_effect_step 0x104f8c 1 (.sib 4 none 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 1492) (RestInside.out (n := 1492) f740 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1493) (ρ' := [(0, 1488), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f3d) f740 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1494) (RestInside.exec (n := 1494) (ρ' := [(0, 1488), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f45) f741 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1495) (RestInside.out (n := 1495) f742 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1496) (ρ' := [(0, 1495), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f4c) f742 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1497) (RestInside.out (n := 1497) f743 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1498) (ρ' := [(0, 1497), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f4e) f743 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1499) (RestInside.exec (n := 1499) (ρ' := [(0, 1497), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f53) f744 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1500) (RestInside.out (n := 1500) f745 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1501) (ρ' := [(0, 1500), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f56) f745 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1502) (RestInside.out (n := 1502) f746 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1503) (ρ' := [(0, 1502), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f59) f746 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1504) (RestInside.out (n := 1504) f747 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1505) (ρ' := [(0, 1504), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f5c) f747 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1506) (RestInside.out (n := 1506) f748 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1507) (ρ' := [(0, 1506), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f61) f748 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1508) (RestInside.out (n := 1508) f749 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1509) (ρ' := [(0, 1506), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1508), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f64) f749 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1510) (RestInside.out (n := 1510) f750 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1511) (ρ' := [(0, 1510), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1508), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f67) f750 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1512) (RestInside.exec (n := 1512) (ρ' := [(0, 1510), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1508), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f6c) f751 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1513) (RestInside.out (n := 1513) f752 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1514) (ρ' := [(0, 1513), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1508), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f6f) f752 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1515) (RestInside.exec (n := 1515) (ρ' := [(0, 1513), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1508), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f74) f753 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1516) (RestInside.exec (n := 1516) (ρ' := [(0, 1513), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1508), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f79) f754 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1517) (RestInside.out (n := 1517) f755 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1518) (ρ' := [(0, 1513), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1517), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f81) f755 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1519) (RestInside.out (n := 1519) f756 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1520) (ρ' := [(0, 1513), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f84) f756 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1521) (RestInside.exec (n := 1521) (ρ' := [(0, 1513), (1, 332), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f8a) f757 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1522) (RestInside.out (n := 1522) f758 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1523) (ρ' := [(0, 1513), (1, 1522), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f8c) f758 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1524) (RestInside.exec (n := 1524) (ρ' := [(0, 1513), (1, 1522), (2, 1365), (3, 1492), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1519), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f91) f759 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10446f_38 code

theorem rest_l10446f_36 [Bindings] (code : CodeMap) :
    Rest (n := 1453) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 1365), (3, 1451), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1443), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      113 0x104ee4 bytes_l10446f_36 b_l10446f_36 := by
  have f720 : InstrSpec 0x104ee4 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104ee4) (xorR32R32Effect 0x104ee4 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ee4 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ee4 0x41 0xdd (by decide) (by decide)) pre_rip
  have f721 : InstrSpec 0x104ee7 [0x01, 0xDB] (fun s => s.RIP = 0x104ee7) (addR32R32Effect 0x104ee7 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104ee7 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x104ee7 0xdb (by decide)) pre_rip
  have f722 : InstrSpec 0x104ee9 [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104ee9) (xorR32R32Effect 0x104ee9 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ee9 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ee9 0x44 0xeb (by decide) (by decide)) pre_rip
  have f723 : InstrSpec 0x104eec [0x66, 0x89, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x104eec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x104eec + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104eec 8 3 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104eec 8 3 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m16_r16_effect_step 0x104eec 3 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f724 : InstrSpec 0x104ef4 [0x0F, 0xB7, 0x9C, 0x24, 0xA6, 0x00, 0x00, 0x00] (LoadPre 0x104ef4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x104ef4 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104ef4 8 3 (.sib 4 none 0 (.d32 0xa6)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104ef4 8 3 (.sib 4 none 0 (.d32 0xa6))).toInstrSpec (movzx_r32_m16_effect_step 0x104ef4 3 (.sib 4 none 0 (.d32 0xa6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f725 : InstrSpec 0x104efc [0x41, 0x89, 0xDD] (fun s => s.RIP = 0x104efc) (movR32R32Effect 0x104efc 3 13 3)
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x104efc 3 13 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104efc 0x41 0xdd (by decide) (by decide)) pre_rip
  have f726 : InstrSpec 0x104eff [0x41, 0xC1, 0xED, 0x02] (fun s => s.RIP = 0x104eff) (shrR32Effect 0x104eff 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR32Effect_footprint 0x104eff 4 13 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104eff 0x41 0xed 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f727 : InstrSpec 0x104f03 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104f03) (xorR32R32Effect 0x104f03 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104f03 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104f03 0x41 0xdd (by decide) (by decide)) pre_rip
  have f728 : InstrSpec 0x104f06 [0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104f06) (andR32Imm32Effect 0x104f06 7 13 0x1320)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104f06 7 13 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104f06 0x41 0xe5 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f729 : InstrSpec 0x104f0d [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104f0d) (xorR32R32Effect 0x104f0d 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104f0d 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104f0d 0x44 0xeb (by decide) (by decide)) pre_rip
  have f730 : InstrSpec 0x104f10 [0x41, 0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x104f10) (shlR32Effect 0x104f10 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR32Effect_footprint 0x104f10 4 13 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104f10 0x41 0xe5 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f731 : InstrSpec 0x104f14 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104f14) (xorR32R32Effect 0x104f14 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104f14 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104f14 0x41 0xdd (by decide) (by decide)) pre_rip
  have f732 : InstrSpec 0x104f17 [0x44, 0x89, 0xE8] (fun s => s.RIP = 0x104f17) (movR32R32Effect 0x104f17 3 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x104f17 3 0 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x104f17 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f733 : InstrSpec 0x104f1a [0xD1, 0xE8] (fun s => s.RIP = 0x104f1a) (shrR32Effect 0x104f1a 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x104f1a 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x104f1a 0xe8 (by decide) (by decide)) pre_rip
  have f734 : InstrSpec 0x104f1c [0x44, 0x31, 0xE8] (fun s => s.RIP = 0x104f1c) (xorR32R32Effect 0x104f1c 3 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104f1c 3 0 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104f1c 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f735 : InstrSpec 0x104f1f [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104f1f) (andEaxImm32Effect 0x104f1f 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x104f1f 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x104f1f 0x5050) pre_rip
  have f736 : InstrSpec 0x104f24 [0x41, 0x31, 0xC5] (fun s => s.RIP = 0x104f24) (xorR32R32Effect 0x104f24 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104f24 3 13 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x104f24 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f737 : InstrSpec 0x104f27 [0x01, 0xC0] (fun s => s.RIP = 0x104f27) (addR32R32Effect 0x104f27 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104f27 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x104f27 0xc0 (by decide)) pre_rip
  have f738 : InstrSpec 0x104f29 [0x44, 0x31, 0xE8] (fun s => s.RIP = 0x104f29) (xorR32R32Effect 0x104f29 3 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104f29 3 0 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104f29 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f739 : InstrSpec 0x104f2c [0x44, 0x0F, 0xB7, 0xAC, 0x24, 0xA2, 0x00, 0x00, 0x00] (LoadPre 0x104f2c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x104f2c + BitVec.ofNat 64 9)) 2) (movzxR32M16Effect 0x104f2c 9 13 (.sib 4 none 0 (.d32 0xa2)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movzxR32M16Effect_footprint 0x104f2c 9 13 (.sib 4 none 0 (.d32 0xa2))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x104f2c 0x44 (by decide) 5 (.sib 4 none 0 (.d32 0xa2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 1453) (RestInside.out (n := 1453) f720 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1454) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1451), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1453), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ee7) f720 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1455) (RestInside.out (n := 1455) f721 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1456) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1455), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1453), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ee9) f721 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1457) (RestInside.out (n := 1457) f722 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1458) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1457), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1453), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104eec) f722 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1459) (RestInside.exec (n := 1459) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1457), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1453), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ef4) f723 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1460) (RestInside.out (n := 1460) f724 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1461) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1460), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1453), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104efc) f724 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1462) (RestInside.out (n := 1462) f725 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1463) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1460), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1462), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104eff) f725 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1464) (RestInside.out (n := 1464) f726 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1465) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1460), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1464), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f03) f726 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1466) (RestInside.out (n := 1466) f727 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1467) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1460), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1466), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f06) f727 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1468) (RestInside.out (n := 1468) f728 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1469) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1460), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1468), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f0d) f728 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1470) (RestInside.out (n := 1470) f729 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1471) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1468), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f10) f729 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1472) (RestInside.out (n := 1472) f730 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1473) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1472), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f14) f730 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1474) (RestInside.out (n := 1474) f731 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1475) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1474), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f17) f731 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1476) (RestInside.out (n := 1476) f732 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1477) (ρ' := [(0, 1476), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1474), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f1a) f732 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1478) (RestInside.out (n := 1478) f733 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1479) (ρ' := [(0, 1478), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1474), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f1c) f733 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1480) (RestInside.out (n := 1480) f734 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1481) (ρ' := [(0, 1480), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1474), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f1f) f734 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1482) (RestInside.out (n := 1482) f735 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1483) (ρ' := [(0, 1482), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1474), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f24) f735 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1484) (RestInside.out (n := 1484) f736 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1485) (ρ' := [(0, 1482), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1484), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f27) f736 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1486) (RestInside.out (n := 1486) f737 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1487) (ρ' := [(0, 1486), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1484), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f29) f737 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1488) (RestInside.out (n := 1488) f738 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1489) (ρ' := [(0, 1488), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1484), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f2c) f738 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1490) (RestInside.out (n := 1490) f739 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1491) (ρ' := [(0, 1488), (1, 332), (2, 1365), (3, 1470), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1490), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104f35) f739 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_37 code

theorem rest_l10446f_35 [Bindings] (code : CodeMap) :
    Rest (n := 1414) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 1365), (3, 1408), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1412), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      133 0x104e95 bytes_l10446f_35 b_l10446f_35 := by
  have f700 : InstrSpec 0x104e95 [0x44, 0x89, 0xEB] (fun s => s.RIP = 0x104e95) (movR32R32Effect 0x104e95 3 3 13)
      [.gpr 13] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x104e95 3 3 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x104e95 0x44 0xeb (by decide) (by decide)) pre_rip
  have f701 : InstrSpec 0x104e98 [0xD1, 0xEB] (fun s => s.RIP = 0x104e98) (shrR32Effect 0x104e98 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x104e98 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x104e98 0xeb (by decide) (by decide)) pre_rip
  have f702 : InstrSpec 0x104e9a [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104e9a) (xorR32R32Effect 0x104e9a 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e9a 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e9a 0x44 0xeb (by decide) (by decide)) pre_rip
  have f703 : InstrSpec 0x104e9d [0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104e9d) (andR32Imm32Effect 0x104e9d 6 3 0x5050)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104e9d 6 3 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104e9d 0xe3 0x5050 (by decide) (by decide)) pre_rip
  have f704 : InstrSpec 0x104ea3 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104ea3) (xorR32R32Effect 0x104ea3 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ea3 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ea3 0x41 0xdd (by decide) (by decide)) pre_rip
  have f705 : InstrSpec 0x104ea6 [0x01, 0xDB] (fun s => s.RIP = 0x104ea6) (addR32R32Effect 0x104ea6 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104ea6 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x104ea6 0xdb (by decide)) pre_rip
  have f706 : InstrSpec 0x104ea8 [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104ea8) (xorR32R32Effect 0x104ea8 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ea8 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ea8 0x44 0xeb (by decide) (by decide)) pre_rip
  have f707 : InstrSpec 0x104eab [0x66, 0x89, 0x9C, 0x24, 0x9E, 0x00, 0x00, 0x00] (StorePre 0x104eab 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x104eab + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104eab 8 3 (.sib 4 none 0 (.d32 0x9e)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104eab 8 3 (.sib 4 none 0 (.d32 0x9e))).toInstrSpec (mov_m16_r16_effect_step 0x104eab 3 (.sib 4 none 0 (.d32 0x9e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f708 : InstrSpec 0x104eb3 [0x0F, 0xB7, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x104eb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x104eb3 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104eb3 8 3 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104eb3 8 3 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (movzx_r32_m16_effect_step 0x104eb3 3 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f709 : InstrSpec 0x104ebb [0x41, 0x89, 0xDD] (fun s => s.RIP = 0x104ebb) (movR32R32Effect 0x104ebb 3 13 3)
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x104ebb 3 13 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104ebb 0x41 0xdd (by decide) (by decide)) pre_rip
  have f710 : InstrSpec 0x104ebe [0x41, 0xC1, 0xED, 0x02] (fun s => s.RIP = 0x104ebe) (shrR32Effect 0x104ebe 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR32Effect_footprint 0x104ebe 4 13 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104ebe 0x41 0xed 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f711 : InstrSpec 0x104ec2 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104ec2) (xorR32R32Effect 0x104ec2 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ec2 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ec2 0x41 0xdd (by decide) (by decide)) pre_rip
  have f712 : InstrSpec 0x104ec5 [0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104ec5) (andR32Imm32Effect 0x104ec5 7 13 0x1320)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104ec5 7 13 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104ec5 0x41 0xe5 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f713 : InstrSpec 0x104ecc [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104ecc) (xorR32R32Effect 0x104ecc 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ecc 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ecc 0x44 0xeb (by decide) (by decide)) pre_rip
  have f714 : InstrSpec 0x104ecf [0x41, 0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x104ecf) (shlR32Effect 0x104ecf 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR32Effect_footprint 0x104ecf 4 13 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104ecf 0x41 0xe5 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f715 : InstrSpec 0x104ed3 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104ed3) (xorR32R32Effect 0x104ed3 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ed3 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ed3 0x41 0xdd (by decide) (by decide)) pre_rip
  have f716 : InstrSpec 0x104ed6 [0x44, 0x89, 0xEB] (fun s => s.RIP = 0x104ed6) (movR32R32Effect 0x104ed6 3 3 13)
      [.gpr 13] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x104ed6 3 3 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x104ed6 0x44 0xeb (by decide) (by decide)) pre_rip
  have f717 : InstrSpec 0x104ed9 [0xD1, 0xEB] (fun s => s.RIP = 0x104ed9) (shrR32Effect 0x104ed9 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x104ed9 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x104ed9 0xeb (by decide) (by decide)) pre_rip
  have f718 : InstrSpec 0x104edb [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104edb) (xorR32R32Effect 0x104edb 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104edb 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104edb 0x44 0xeb (by decide) (by decide)) pre_rip
  have f719 : InstrSpec 0x104ede [0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104ede) (andR32Imm32Effect 0x104ede 6 3 0x5050)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104ede 6 3 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104ede 0xe3 0x5050 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1414) (RestInside.out (n := 1414) f700 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1415) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1414), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1412), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e98) f700 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1416) (RestInside.out (n := 1416) f701 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1417) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1416), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1412), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e9a) f701 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1418) (RestInside.out (n := 1418) f702 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1419) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1418), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1412), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e9d) f702 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1420) (RestInside.out (n := 1420) f703 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1421) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1420), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1412), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ea3) f703 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1422) (RestInside.out (n := 1422) f704 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1423) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1420), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1422), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ea6) f704 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1424) (RestInside.out (n := 1424) f705 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1425) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1424), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1422), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ea8) f705 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1426) (RestInside.out (n := 1426) f706 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1427) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1426), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1422), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104eab) f706 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1428) (RestInside.exec (n := 1428) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1426), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1422), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104eb3) f707 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1429) (RestInside.out (n := 1429) f708 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1430) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1429), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1422), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ebb) f708 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1431) (RestInside.out (n := 1431) f709 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1432) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1429), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1431), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ebe) f709 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1433) (RestInside.out (n := 1433) f710 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1434) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1429), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1433), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ec2) f710 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1435) (RestInside.out (n := 1435) f711 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1436) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1429), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1435), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ec5) f711 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1437) (RestInside.out (n := 1437) f712 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1438) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1429), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1437), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ecc) f712 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1439) (RestInside.out (n := 1439) f713 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1440) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1439), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1437), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ecf) f713 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1441) (RestInside.out (n := 1441) f714 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1442) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1439), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1441), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ed3) f714 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1443) (RestInside.out (n := 1443) f715 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1444) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1439), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1443), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ed6) f715 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1445) (RestInside.out (n := 1445) f716 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1446) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1445), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1443), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ed9) f716 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1447) (RestInside.out (n := 1447) f717 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1448) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1447), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1443), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104edb) f717 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1449) (RestInside.out (n := 1449) f718 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1450) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1449), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1443), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ede) f718 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1451) (RestInside.out (n := 1451) f719 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1452) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1451), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1443), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ee4) f719 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_36 code

theorem rest_l10446f_34 [Bindings] (code : CodeMap) :
    Rest (n := 1375) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 1365), (3, 1367), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1373), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      153 0x104e43 bytes_l10446f_34 b_l10446f_34 := by
  have f680 : InstrSpec 0x104e43 [0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104e43) (andR32Imm32Effect 0x104e43 7 13 0x1320)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104e43 7 13 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104e43 0x41 0xe5 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f681 : InstrSpec 0x104e4a [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104e4a) (xorR32R32Effect 0x104e4a 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e4a 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e4a 0x44 0xeb (by decide) (by decide)) pre_rip
  have f682 : InstrSpec 0x104e4d [0x41, 0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x104e4d) (shlR32Effect 0x104e4d 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR32Effect_footprint 0x104e4d 4 13 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104e4d 0x41 0xe5 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f683 : InstrSpec 0x104e51 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104e51) (xorR32R32Effect 0x104e51 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e51 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e51 0x41 0xdd (by decide) (by decide)) pre_rip
  have f684 : InstrSpec 0x104e54 [0x44, 0x89, 0xEB] (fun s => s.RIP = 0x104e54) (movR32R32Effect 0x104e54 3 3 13)
      [.gpr 13] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x104e54 3 3 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x104e54 0x44 0xeb (by decide) (by decide)) pre_rip
  have f685 : InstrSpec 0x104e57 [0xD1, 0xEB] (fun s => s.RIP = 0x104e57) (shrR32Effect 0x104e57 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x104e57 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x104e57 0xeb (by decide) (by decide)) pre_rip
  have f686 : InstrSpec 0x104e59 [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104e59) (xorR32R32Effect 0x104e59 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e59 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e59 0x44 0xeb (by decide) (by decide)) pre_rip
  have f687 : InstrSpec 0x104e5c [0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104e5c) (andR32Imm32Effect 0x104e5c 6 3 0x5050)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104e5c 6 3 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104e5c 0xe3 0x5050 (by decide) (by decide)) pre_rip
  have f688 : InstrSpec 0x104e62 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104e62) (xorR32R32Effect 0x104e62 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e62 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e62 0x41 0xdd (by decide) (by decide)) pre_rip
  have f689 : InstrSpec 0x104e65 [0x01, 0xDB] (fun s => s.RIP = 0x104e65) (addR32R32Effect 0x104e65 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104e65 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x104e65 0xdb (by decide)) pre_rip
  have f690 : InstrSpec 0x104e67 [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104e67) (xorR32R32Effect 0x104e67 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e67 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e67 0x44 0xeb (by decide) (by decide)) pre_rip
  have f691 : InstrSpec 0x104e6a [0x66, 0x89, 0x9C, 0x24, 0x9C, 0x00, 0x00, 0x00] (StorePre 0x104e6a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x104e6a + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104e6a 8 3 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104e6a 8 3 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (mov_m16_r16_effect_step 0x104e6a 3 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f692 : InstrSpec 0x104e72 [0x0F, 0xB7, 0x9C, 0x24, 0x9E, 0x00, 0x00, 0x00] (LoadPre 0x104e72 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x104e72 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104e72 8 3 (.sib 4 none 0 (.d32 0x9e)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104e72 8 3 (.sib 4 none 0 (.d32 0x9e))).toInstrSpec (movzx_r32_m16_effect_step 0x104e72 3 (.sib 4 none 0 (.d32 0x9e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f693 : InstrSpec 0x104e7a [0x41, 0x89, 0xDD] (fun s => s.RIP = 0x104e7a) (movR32R32Effect 0x104e7a 3 13 3)
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x104e7a 3 13 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104e7a 0x41 0xdd (by decide) (by decide)) pre_rip
  have f694 : InstrSpec 0x104e7d [0x41, 0xC1, 0xED, 0x02] (fun s => s.RIP = 0x104e7d) (shrR32Effect 0x104e7d 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR32Effect_footprint 0x104e7d 4 13 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104e7d 0x41 0xed 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f695 : InstrSpec 0x104e81 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104e81) (xorR32R32Effect 0x104e81 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e81 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e81 0x41 0xdd (by decide) (by decide)) pre_rip
  have f696 : InstrSpec 0x104e84 [0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104e84) (andR32Imm32Effect 0x104e84 7 13 0x1320)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104e84 7 13 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104e84 0x41 0xe5 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f697 : InstrSpec 0x104e8b [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104e8b) (xorR32R32Effect 0x104e8b 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e8b 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e8b 0x44 0xeb (by decide) (by decide)) pre_rip
  have f698 : InstrSpec 0x104e8e [0x41, 0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x104e8e) (shlR32Effect 0x104e8e 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR32Effect_footprint 0x104e8e 4 13 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104e8e 0x41 0xe5 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f699 : InstrSpec 0x104e92 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104e92) (xorR32R32Effect 0x104e92 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e92 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e92 0x41 0xdd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1375) (RestInside.out (n := 1375) f680 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1376) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1367), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1375), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e4a) f680 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1377) (RestInside.out (n := 1377) f681 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1378) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1377), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1375), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e4d) f681 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1379) (RestInside.out (n := 1379) f682 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1380) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1377), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1379), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e51) f682 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1381) (RestInside.out (n := 1381) f683 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1382) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1377), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1381), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e54) f683 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1383) (RestInside.out (n := 1383) f684 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1384) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1383), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1381), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e57) f684 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1385) (RestInside.out (n := 1385) f685 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1386) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1385), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1381), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e59) f685 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1387) (RestInside.out (n := 1387) f686 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1388) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1387), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1381), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e5c) f686 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1389) (RestInside.out (n := 1389) f687 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1390) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1389), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1381), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e62) f687 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1391) (RestInside.out (n := 1391) f688 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1392) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1389), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1391), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e65) f688 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1393) (RestInside.out (n := 1393) f689 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1394) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1393), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1391), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e67) f689 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1395) (RestInside.out (n := 1395) f690 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1396) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1395), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1391), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e6a) f690 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1397) (RestInside.exec (n := 1397) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1395), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1391), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e72) f691 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1398) (RestInside.out (n := 1398) f692 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1399) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1398), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1391), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e7a) f692 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1400) (RestInside.out (n := 1400) f693 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1401) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1398), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1400), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e7d) f693 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1402) (RestInside.out (n := 1402) f694 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1403) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1398), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1402), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e81) f694 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1404) (RestInside.out (n := 1404) f695 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1405) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1398), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1404), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e84) f695 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1406) (RestInside.out (n := 1406) f696 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1407) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1398), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1406), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e8b) f696 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1408) (RestInside.out (n := 1408) f697 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1409) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1408), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1406), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e8e) f697 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1410) (RestInside.out (n := 1410) f698 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1411) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1408), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1410), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e92) f698 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1412) (RestInside.out (n := 1412) f699 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1413) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1408), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1412), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e95) f699 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_35 code

theorem rest_l10446f_33 [Bindings] (code : CodeMap) :
    Rest (n := 1335) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1333), (13, 1331), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      173 0x104df5 bytes_l10446f_33 b_l10446f_33 := by
  have f660 : InstrSpec 0x104df5 [0x45, 0x31, 0xEC] (fun s => s.RIP = 0x104df5) (xorR32R32Effect 0x104df5 3 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104df5 3 12 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104df5 0x45 0xec (by decide) (by decide)) pre_rip
  have f661 : InstrSpec 0x104df8 [0x0F, 0xB7, 0x9C, 0x24, 0x9A, 0x00, 0x00, 0x00] (LoadPre 0x104df8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9a)) s (0x104df8 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104df8 8 3 (.sib 4 none 0 (.d32 0x9a)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104df8 8 3 (.sib 4 none 0 (.d32 0x9a))).toInstrSpec (movzx_r32_m16_effect_step 0x104df8 3 (.sib 4 none 0 (.d32 0x9a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f662 : InstrSpec 0x104e00 [0x41, 0x89, 0xDD] (fun s => s.RIP = 0x104e00) (movR32R32Effect 0x104e00 3 13 3)
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x104e00 3 13 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104e00 0x41 0xdd (by decide) (by decide)) pre_rip
  have f663 : InstrSpec 0x104e03 [0x41, 0xC1, 0xED, 0x02] (fun s => s.RIP = 0x104e03) (shrR32Effect 0x104e03 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR32Effect_footprint 0x104e03 4 13 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104e03 0x41 0xed 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f664 : InstrSpec 0x104e07 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104e07) (xorR32R32Effect 0x104e07 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e07 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e07 0x41 0xdd (by decide) (by decide)) pre_rip
  have f665 : InstrSpec 0x104e0a [0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104e0a) (andR32Imm32Effect 0x104e0a 7 13 0x1320)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104e0a 7 13 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104e0a 0x41 0xe5 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f666 : InstrSpec 0x104e11 [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104e11) (xorR32R32Effect 0x104e11 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e11 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e11 0x44 0xeb (by decide) (by decide)) pre_rip
  have f667 : InstrSpec 0x104e14 [0x41, 0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x104e14) (shlR32Effect 0x104e14 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR32Effect_footprint 0x104e14 4 13 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104e14 0x41 0xe5 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f668 : InstrSpec 0x104e18 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104e18) (xorR32R32Effect 0x104e18 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e18 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e18 0x41 0xdd (by decide) (by decide)) pre_rip
  have f669 : InstrSpec 0x104e1b [0x44, 0x89, 0xEA] (fun s => s.RIP = 0x104e1b) (movR32R32Effect 0x104e1b 3 2 13)
      [.gpr 13] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x104e1b 3 2 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x104e1b 0x44 0xea (by decide) (by decide)) pre_rip
  have f670 : InstrSpec 0x104e1e [0xD1, 0xEA] (fun s => s.RIP = 0x104e1e) (shrR32Effect 0x104e1e 2 2 1)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x104e1e 2 2 1).toInstrSpec (shr_r32_one_effect_step 0x104e1e 0xea (by decide) (by decide)) pre_rip
  have f671 : InstrSpec 0x104e20 [0x44, 0x31, 0xEA] (fun s => s.RIP = 0x104e20) (xorR32R32Effect 0x104e20 3 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e20 3 2 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e20 0x44 0xea (by decide) (by decide)) pre_rip
  have f672 : InstrSpec 0x104e23 [0x81, 0xE2, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104e23) (andR32Imm32Effect 0x104e23 6 2 0x5050)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104e23 6 2 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104e23 0xe2 0x5050 (by decide) (by decide)) pre_rip
  have f673 : InstrSpec 0x104e29 [0x41, 0x31, 0xD5] (fun s => s.RIP = 0x104e29) (xorR32R32Effect 0x104e29 3 13 2)
      [.gpr 13, .gpr 2] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e29 3 13 2).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e29 0x41 0xd5 (by decide) (by decide)) pre_rip
  have f674 : InstrSpec 0x104e2c [0x01, 0xD2] (fun s => s.RIP = 0x104e2c) (addR32R32Effect 0x104e2c 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104e2c 2 2 2).toInstrSpec (add_r32_r32_effect_step 0x104e2c 0xd2 (by decide)) pre_rip
  have f675 : InstrSpec 0x104e2e [0x44, 0x31, 0xEA] (fun s => s.RIP = 0x104e2e) (xorR32R32Effect 0x104e2e 3 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e2e 3 2 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e2e 0x44 0xea (by decide) (by decide)) pre_rip
  have f676 : InstrSpec 0x104e31 [0x0F, 0xB7, 0x9C, 0x24, 0x9C, 0x00, 0x00, 0x00] (LoadPre 0x104e31 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x104e31 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104e31 8 3 (.sib 4 none 0 (.d32 0x9c)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104e31 8 3 (.sib 4 none 0 (.d32 0x9c))).toInstrSpec (movzx_r32_m16_effect_step 0x104e31 3 (.sib 4 none 0 (.d32 0x9c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f677 : InstrSpec 0x104e39 [0x41, 0x89, 0xDD] (fun s => s.RIP = 0x104e39) (movR32R32Effect 0x104e39 3 13 3)
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x104e39 3 13 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104e39 0x41 0xdd (by decide) (by decide)) pre_rip
  have f678 : InstrSpec 0x104e3c [0x41, 0xC1, 0xED, 0x02] (fun s => s.RIP = 0x104e3c) (shrR32Effect 0x104e3c 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR32Effect_footprint 0x104e3c 4 13 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104e3c 0x41 0xed 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f679 : InstrSpec 0x104e40 [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104e40) (xorR32R32Effect 0x104e40 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104e40 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104e40 0x41 0xdd (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1335) (RestInside.out (n := 1335) f660 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1336) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1331), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104df8) f660 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1337) (RestInside.out (n := 1337) f661 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1338) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1337), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1331), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e00) f661 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1339) (RestInside.out (n := 1339) f662 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1340) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1337), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1339), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e03) f662 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1341) (RestInside.out (n := 1341) f663 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1342) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1337), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1341), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e07) f663 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1343) (RestInside.out (n := 1343) f664 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1344) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1337), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1343), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e0a) f664 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1345) (RestInside.out (n := 1345) f665 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1346) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1337), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1345), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e11) f665 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1347) (RestInside.out (n := 1347) f666 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1348) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1347), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1345), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e14) f666 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1349) (RestInside.out (n := 1349) f667 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1350) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1347), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1349), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e18) f667 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1351) (RestInside.out (n := 1351) f668 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1352) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1347), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1351), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e1b) f668 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1353) (RestInside.out (n := 1353) f669 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1354) (ρ' := [(0, 315), (1, 332), (2, 1353), (3, 1347), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1351), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e1e) f669 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1355) (RestInside.out (n := 1355) f670 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1356) (ρ' := [(0, 315), (1, 332), (2, 1355), (3, 1347), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1351), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e20) f670 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1357) (RestInside.out (n := 1357) f671 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1358) (ρ' := [(0, 315), (1, 332), (2, 1357), (3, 1347), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1351), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e23) f671 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1359) (RestInside.out (n := 1359) f672 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1360) (ρ' := [(0, 315), (1, 332), (2, 1359), (3, 1347), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1351), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e29) f672 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1361) (RestInside.out (n := 1361) f673 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1362) (ρ' := [(0, 315), (1, 332), (2, 1359), (3, 1347), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1361), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e2c) f673 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1363) (RestInside.out (n := 1363) f674 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1364) (ρ' := [(0, 315), (1, 332), (2, 1363), (3, 1347), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1361), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e2e) f674 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1365) (RestInside.out (n := 1365) f675 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1366) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1347), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1361), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e31) f675 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1367) (RestInside.out (n := 1367) f676 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1368) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1367), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1361), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e39) f676 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1369) (RestInside.out (n := 1369) f677 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1370) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1367), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1369), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e3c) f677 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1371) (RestInside.out (n := 1371) f678 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1372) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1367), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1371), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e40) f678 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1373) (RestInside.out (n := 1373) f679 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1374) (ρ' := [(0, 315), (1, 332), (2, 1365), (3, 1367), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1335), (13, 1373), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104e43) f679 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_34 code

theorem rest_l10446f_32 [Bindings] (code : CodeMap) :
    Rest (n := 1296) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 1294), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1290), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      193 0x104da3 bytes_l10446f_32 b_l10446f_32 := by
  have f640 : InstrSpec 0x104da3 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104da3) (xorR32R32Effect 0x104da3 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104da3 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104da3 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f641 : InstrSpec 0x104da6 [0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104da6) (andR32Imm32Effect 0x104da6 6 3 0x5050)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104da6 6 3 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104da6 0xe3 0x5050 (by decide) (by decide)) pre_rip
  have f642 : InstrSpec 0x104dac [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104dac) (xorR32R32Effect 0x104dac 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104dac 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104dac 0x41 0xdc (by decide) (by decide)) pre_rip
  have f643 : InstrSpec 0x104daf [0x01, 0xDB] (fun s => s.RIP = 0x104daf) (addR32R32Effect 0x104daf 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104daf 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x104daf 0xdb (by decide)) pre_rip
  have f644 : InstrSpec 0x104db1 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104db1) (xorR32R32Effect 0x104db1 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104db1 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104db1 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f645 : InstrSpec 0x104db4 [0x66, 0x89, 0x9C, 0x24, 0x86, 0x00, 0x00, 0x00] (StorePre 0x104db4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x86)) s (0x104db4 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104db4 8 3 (.sib 4 none 0 (.d32 0x86)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104db4 8 3 (.sib 4 none 0 (.d32 0x86))).toInstrSpec (mov_m16_r16_effect_step 0x104db4 3 (.sib 4 none 0 (.d32 0x86)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f646 : InstrSpec 0x104dbc [0x0F, 0xB7, 0x9C, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x104dbc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x104dbc + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104dbc 8 3 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104dbc 8 3 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (movzx_r32_m16_effect_step 0x104dbc 3 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f647 : InstrSpec 0x104dc4 [0x41, 0x89, 0xDD] (fun s => s.RIP = 0x104dc4) (movR32R32Effect 0x104dc4 3 13 3)
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x104dc4 3 13 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104dc4 0x41 0xdd (by decide) (by decide)) pre_rip
  have f648 : InstrSpec 0x104dc7 [0x41, 0xC1, 0xED, 0x02] (fun s => s.RIP = 0x104dc7) (shrR32Effect 0x104dc7 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR32Effect_footprint 0x104dc7 4 13 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104dc7 0x41 0xed 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f649 : InstrSpec 0x104dcb [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104dcb) (xorR32R32Effect 0x104dcb 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104dcb 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104dcb 0x41 0xdd (by decide) (by decide)) pre_rip
  have f650 : InstrSpec 0x104dce [0x41, 0x81, 0xE5, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104dce) (andR32Imm32Effect 0x104dce 7 13 0x1320)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104dce 7 13 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104dce 0x41 0xe5 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f651 : InstrSpec 0x104dd5 [0x44, 0x31, 0xEB] (fun s => s.RIP = 0x104dd5) (xorR32R32Effect 0x104dd5 3 3 13)
      [.gpr 3, .gpr 13] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104dd5 3 3 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104dd5 0x44 0xeb (by decide) (by decide)) pre_rip
  have f652 : InstrSpec 0x104dd8 [0x41, 0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x104dd8) (shlR32Effect 0x104dd8 4 13 2)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR32Effect_footprint 0x104dd8 4 13 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104dd8 0x41 0xe5 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f653 : InstrSpec 0x104ddc [0x41, 0x31, 0xDD] (fun s => s.RIP = 0x104ddc) (xorR32R32Effect 0x104ddc 3 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ddc 3 13 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ddc 0x41 0xdd (by decide) (by decide)) pre_rip
  have f654 : InstrSpec 0x104ddf [0x45, 0x89, 0xEC] (fun s => s.RIP = 0x104ddf) (movR32R32Effect 0x104ddf 3 12 13)
      [.gpr 13] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x104ddf 3 12 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x104ddf 0x45 0xec (by decide) (by decide)) pre_rip
  have f655 : InstrSpec 0x104de2 [0x41, 0xD1, 0xEC] (fun s => s.RIP = 0x104de2) (shrR32Effect 0x104de2 3 12 1)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x104de2 3 12 1).toInstrSpec (shr_r32_one_rex_effect_step 0x104de2 0x41 0xec (by decide) (by decide) (by decide)) pre_rip
  have f656 : InstrSpec 0x104de5 [0x45, 0x31, 0xEC] (fun s => s.RIP = 0x104de5) (xorR32R32Effect 0x104de5 3 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104de5 3 12 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x104de5 0x45 0xec (by decide) (by decide)) pre_rip
  have f657 : InstrSpec 0x104de8 [0x41, 0x81, 0xE4, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104de8) (andR32Imm32Effect 0x104de8 7 12 0x5050)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104de8 7 12 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104de8 0x41 0xe4 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f658 : InstrSpec 0x104def [0x45, 0x31, 0xE5] (fun s => s.RIP = 0x104def) (xorR32R32Effect 0x104def 3 13 12)
      [.gpr 13, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104def 3 13 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104def 0x45 0xe5 (by decide) (by decide)) pre_rip
  have f659 : InstrSpec 0x104df2 [0x45, 0x01, 0xE4] (fun s => s.RIP = 0x104df2) (addR32R32Effect 0x104df2 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104df2 3 12 12).toInstrSpec (add_r32_r32_rex_effect_step 0x104df2 0x45 0xe4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1296) (RestInside.out (n := 1296) f640 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1297) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1296), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1290), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104da6) f640 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1298) (RestInside.out (n := 1298) f641 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1299) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1298), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1290), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dac) f641 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1300) (RestInside.out (n := 1300) f642 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1301) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1298), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104daf) f642 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1302) (RestInside.out (n := 1302) f643 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1303) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1302), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104db1) f643 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1304) (RestInside.out (n := 1304) f644 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1305) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1304), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104db4) f644 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1306) (RestInside.exec (n := 1306) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1304), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dbc) f645 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1307) (RestInside.out (n := 1307) f646 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1308) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1307), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dc4) f646 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1309) (RestInside.out (n := 1309) f647 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1310) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1307), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (13, 1309), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dc7) f647 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1311) (RestInside.out (n := 1311) f648 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1312) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1307), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (13, 1311), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dcb) f648 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1313) (RestInside.out (n := 1313) f649 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1314) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1307), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (13, 1313), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dce) f649 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1315) (RestInside.out (n := 1315) f650 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1316) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1307), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (13, 1315), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dd5) f650 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1317) (RestInside.out (n := 1317) f651 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1318) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (13, 1315), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104dd8) f651 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1319) (RestInside.out (n := 1319) f652 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1320) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (13, 1319), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ddc) f652 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1321) (RestInside.out (n := 1321) f653 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1322) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1300), (13, 1321), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ddf) f653 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1323) (RestInside.out (n := 1323) f654 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1324) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1323), (13, 1321), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104de2) f654 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1325) (RestInside.out (n := 1325) f655 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1326) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1325), (13, 1321), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104de5) f655 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1327) (RestInside.out (n := 1327) f656 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1328) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1327), (13, 1321), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104de8) f656 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1329) (RestInside.out (n := 1329) f657 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1330) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1329), (13, 1321), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104def) f657 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1331) (RestInside.out (n := 1331) f658 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1332) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1329), (13, 1331), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104df2) f658 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1333) (RestInside.out (n := 1333) f659 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1334) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1317), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1333), (13, 1331), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104df5) f659 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_33 code

theorem rest_l10446f_31 [Bindings] (code : CodeMap) :
    Rest (n := 1257) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 1255), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1253), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      213 0x104d56 bytes_l10446f_31 b_l10446f_31 := by
  have f620 : InstrSpec 0x104d56 [0x41, 0xC1, 0xE4, 0x02] (fun s => s.RIP = 0x104d56) (shlR32Effect 0x104d56 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x104d56 4 12 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104d56 0x41 0xe4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f621 : InstrSpec 0x104d5a [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104d5a) (xorR32R32Effect 0x104d5a 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d5a 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d5a 0x41 0xdc (by decide) (by decide)) pre_rip
  have f622 : InstrSpec 0x104d5d [0x44, 0x89, 0xE3] (fun s => s.RIP = 0x104d5d) (movR32R32Effect 0x104d5d 3 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x104d5d 3 3 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x104d5d 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f623 : InstrSpec 0x104d60 [0xD1, 0xEB] (fun s => s.RIP = 0x104d60) (shrR32Effect 0x104d60 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x104d60 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x104d60 0xeb (by decide) (by decide)) pre_rip
  have f624 : InstrSpec 0x104d62 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104d62) (xorR32R32Effect 0x104d62 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d62 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d62 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f625 : InstrSpec 0x104d65 [0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104d65) (andR32Imm32Effect 0x104d65 6 3 0x5050)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104d65 6 3 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104d65 0xe3 0x5050 (by decide) (by decide)) pre_rip
  have f626 : InstrSpec 0x104d6b [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104d6b) (xorR32R32Effect 0x104d6b 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d6b 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d6b 0x41 0xdc (by decide) (by decide)) pre_rip
  have f627 : InstrSpec 0x104d6e [0x01, 0xDB] (fun s => s.RIP = 0x104d6e) (addR32R32Effect 0x104d6e 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104d6e 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x104d6e 0xdb (by decide)) pre_rip
  have f628 : InstrSpec 0x104d70 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104d70) (xorR32R32Effect 0x104d70 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d70 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d70 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f629 : InstrSpec 0x104d73 [0x66, 0x89, 0x9C, 0x24, 0x84, 0x00, 0x00, 0x00] (StorePre 0x104d73 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x104d73 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104d73 8 3 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104d73 8 3 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (mov_m16_r16_effect_step 0x104d73 3 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f630 : InstrSpec 0x104d7b [0x0F, 0xB7, 0x9C, 0x24, 0x86, 0x00, 0x00, 0x00] (LoadPre 0x104d7b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x86)) s (0x104d7b + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104d7b 8 3 (.sib 4 none 0 (.d32 0x86)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104d7b 8 3 (.sib 4 none 0 (.d32 0x86))).toInstrSpec (movzx_r32_m16_effect_step 0x104d7b 3 (.sib 4 none 0 (.d32 0x86)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f631 : InstrSpec 0x104d83 [0x41, 0x89, 0xDC] (fun s => s.RIP = 0x104d83) (movR32R32Effect 0x104d83 3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x104d83 3 12 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104d83 0x41 0xdc (by decide) (by decide)) pre_rip
  have f632 : InstrSpec 0x104d86 [0x41, 0xC1, 0xEC, 0x02] (fun s => s.RIP = 0x104d86) (shrR32Effect 0x104d86 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x104d86 4 12 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104d86 0x41 0xec 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f633 : InstrSpec 0x104d8a [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104d8a) (xorR32R32Effect 0x104d8a 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d8a 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d8a 0x41 0xdc (by decide) (by decide)) pre_rip
  have f634 : InstrSpec 0x104d8d [0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x104d8d) (andR32Imm32Effect 0x104d8d 7 12 0x2310)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104d8d 7 12 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x104d8d 0x41 0xe4 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f635 : InstrSpec 0x104d94 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104d94) (xorR32R32Effect 0x104d94 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d94 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d94 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f636 : InstrSpec 0x104d97 [0x41, 0xC1, 0xE4, 0x02] (fun s => s.RIP = 0x104d97) (shlR32Effect 0x104d97 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x104d97 4 12 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104d97 0x41 0xe4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f637 : InstrSpec 0x104d9b [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104d9b) (xorR32R32Effect 0x104d9b 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d9b 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d9b 0x41 0xdc (by decide) (by decide)) pre_rip
  have f638 : InstrSpec 0x104d9e [0x44, 0x89, 0xE3] (fun s => s.RIP = 0x104d9e) (movR32R32Effect 0x104d9e 3 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x104d9e 3 3 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x104d9e 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f639 : InstrSpec 0x104da1 [0xD1, 0xEB] (fun s => s.RIP = 0x104da1) (shrR32Effect 0x104da1 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x104da1 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x104da1 0xeb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1257) (RestInside.out (n := 1257) f620 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1258) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1255), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1257), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d5a) f620 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1259) (RestInside.out (n := 1259) f621 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1260) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1255), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1259), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d5d) f621 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1261) (RestInside.out (n := 1261) f622 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1262) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1261), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1259), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d60) f622 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1263) (RestInside.out (n := 1263) f623 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1264) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1263), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1259), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d62) f623 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1265) (RestInside.out (n := 1265) f624 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1266) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1265), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1259), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d65) f624 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1267) (RestInside.out (n := 1267) f625 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1268) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1267), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1259), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d6b) f625 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1269) (RestInside.out (n := 1269) f626 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1270) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1267), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1269), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d6e) f626 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1271) (RestInside.out (n := 1271) f627 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1272) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1271), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1269), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d70) f627 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1273) (RestInside.out (n := 1273) f628 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1274) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1273), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1269), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d73) f628 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1275) (RestInside.exec (n := 1275) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1273), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1269), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d7b) f629 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1276) (RestInside.out (n := 1276) f630 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1277) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1276), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1269), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d83) f630 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1278) (RestInside.out (n := 1278) f631 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1279) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1276), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1278), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d86) f631 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1280) (RestInside.out (n := 1280) f632 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1281) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1276), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1280), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d8a) f632 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1282) (RestInside.out (n := 1282) f633 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1283) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1276), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1282), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d8d) f633 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1284) (RestInside.out (n := 1284) f634 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1285) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1276), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1284), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d94) f634 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1286) (RestInside.out (n := 1286) f635 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1287) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1286), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1284), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d97) f635 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1288) (RestInside.out (n := 1288) f636 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1289) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1286), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1288), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d9b) f636 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1290) (RestInside.out (n := 1290) f637 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1291) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1286), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1290), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d9e) f637 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1292) (RestInside.out (n := 1292) f638 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1293) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1292), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1290), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104da1) f638 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1294) (RestInside.out (n := 1294) f639 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1295) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1294), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1290), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104da3) f639 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_32 code

theorem rest_l10446f_30 [Bindings] (code : CodeMap) :
    Rest (n := 1218) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 1214), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1216), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      233 0x104d04 bytes_l10446f_30 b_l10446f_30 := by
  have f600 : InstrSpec 0x104d04 [0x41, 0xC1, 0xEC, 0x02] (fun s => s.RIP = 0x104d04) (shrR32Effect 0x104d04 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x104d04 4 12 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104d04 0x41 0xec 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f601 : InstrSpec 0x104d08 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104d08) (xorR32R32Effect 0x104d08 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d08 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d08 0x41 0xdc (by decide) (by decide)) pre_rip
  have f602 : InstrSpec 0x104d0b [0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x104d0b) (andR32Imm32Effect 0x104d0b 7 12 0x2310)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104d0b 7 12 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x104d0b 0x41 0xe4 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f603 : InstrSpec 0x104d12 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104d12) (xorR32R32Effect 0x104d12 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d12 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d12 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f604 : InstrSpec 0x104d15 [0x41, 0xC1, 0xE4, 0x02] (fun s => s.RIP = 0x104d15) (shlR32Effect 0x104d15 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x104d15 4 12 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104d15 0x41 0xe4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f605 : InstrSpec 0x104d19 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104d19) (xorR32R32Effect 0x104d19 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d19 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d19 0x41 0xdc (by decide) (by decide)) pre_rip
  have f606 : InstrSpec 0x104d1c [0x44, 0x89, 0xE3] (fun s => s.RIP = 0x104d1c) (movR32R32Effect 0x104d1c 3 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x104d1c 3 3 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x104d1c 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f607 : InstrSpec 0x104d1f [0xD1, 0xEB] (fun s => s.RIP = 0x104d1f) (shrR32Effect 0x104d1f 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x104d1f 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x104d1f 0xeb (by decide) (by decide)) pre_rip
  have f608 : InstrSpec 0x104d21 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104d21) (xorR32R32Effect 0x104d21 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d21 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d21 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f609 : InstrSpec 0x104d24 [0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104d24) (andR32Imm32Effect 0x104d24 6 3 0x5050)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104d24 6 3 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104d24 0xe3 0x5050 (by decide) (by decide)) pre_rip
  have f610 : InstrSpec 0x104d2a [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104d2a) (xorR32R32Effect 0x104d2a 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d2a 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d2a 0x41 0xdc (by decide) (by decide)) pre_rip
  have f611 : InstrSpec 0x104d2d [0x01, 0xDB] (fun s => s.RIP = 0x104d2d) (addR32R32Effect 0x104d2d 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104d2d 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x104d2d 0xdb (by decide)) pre_rip
  have f612 : InstrSpec 0x104d2f [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104d2f) (xorR32R32Effect 0x104d2f 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d2f 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d2f 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f613 : InstrSpec 0x104d32 [0x66, 0x89, 0x9C, 0x24, 0x82, 0x00, 0x00, 0x00] (StorePre 0x104d32 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x104d32 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104d32 8 3 (.sib 4 none 0 (.d32 0x82)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104d32 8 3 (.sib 4 none 0 (.d32 0x82))).toInstrSpec (mov_m16_r16_effect_step 0x104d32 3 (.sib 4 none 0 (.d32 0x82)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f614 : InstrSpec 0x104d3a [0x0F, 0xB7, 0x9C, 0x24, 0x84, 0x00, 0x00, 0x00] (LoadPre 0x104d3a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x104d3a + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104d3a 8 3 (.sib 4 none 0 (.d32 0x84)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104d3a 8 3 (.sib 4 none 0 (.d32 0x84))).toInstrSpec (movzx_r32_m16_effect_step 0x104d3a 3 (.sib 4 none 0 (.d32 0x84)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f615 : InstrSpec 0x104d42 [0x41, 0x89, 0xDC] (fun s => s.RIP = 0x104d42) (movR32R32Effect 0x104d42 3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x104d42 3 12 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104d42 0x41 0xdc (by decide) (by decide)) pre_rip
  have f616 : InstrSpec 0x104d45 [0x41, 0xC1, 0xEC, 0x02] (fun s => s.RIP = 0x104d45) (shrR32Effect 0x104d45 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x104d45 4 12 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104d45 0x41 0xec 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f617 : InstrSpec 0x104d49 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104d49) (xorR32R32Effect 0x104d49 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d49 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d49 0x41 0xdc (by decide) (by decide)) pre_rip
  have f618 : InstrSpec 0x104d4c [0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x104d4c) (andR32Imm32Effect 0x104d4c 7 12 0x2310)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104d4c 7 12 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x104d4c 0x41 0xe4 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f619 : InstrSpec 0x104d53 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104d53) (xorR32R32Effect 0x104d53 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104d53 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104d53 0x44 0xe3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1218) (RestInside.out (n := 1218) f600 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1219) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1214), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1218), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d08) f600 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1220) (RestInside.out (n := 1220) f601 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1221) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1214), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1220), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d0b) f601 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1222) (RestInside.out (n := 1222) f602 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1223) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1214), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1222), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d12) f602 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1224) (RestInside.out (n := 1224) f603 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1225) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1224), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1222), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d15) f603 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1226) (RestInside.out (n := 1226) f604 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1227) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1224), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1226), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d19) f604 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1228) (RestInside.out (n := 1228) f605 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1229) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1224), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1228), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d1c) f605 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1230) (RestInside.out (n := 1230) f606 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1231) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1230), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1228), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d1f) f606 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1232) (RestInside.out (n := 1232) f607 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1233) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1232), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1228), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d21) f607 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1234) (RestInside.out (n := 1234) f608 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1235) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1234), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1228), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d24) f608 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1236) (RestInside.out (n := 1236) f609 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1237) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1236), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1228), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d2a) f609 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1238) (RestInside.out (n := 1238) f610 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1239) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1236), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1238), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d2d) f610 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1240) (RestInside.out (n := 1240) f611 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1241) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1240), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1238), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d2f) f611 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1242) (RestInside.out (n := 1242) f612 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1243) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1242), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1238), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d32) f612 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1244) (RestInside.exec (n := 1244) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1242), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1238), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d3a) f613 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1245) (RestInside.out (n := 1245) f614 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1246) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1245), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1238), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d42) f614 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1247) (RestInside.out (n := 1247) f615 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1248) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1245), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1247), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d45) f615 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1249) (RestInside.out (n := 1249) f616 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1250) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1245), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1249), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d49) f616 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1251) (RestInside.out (n := 1251) f617 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1252) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1245), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1251), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d4c) f617 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1253) (RestInside.out (n := 1253) f618 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1254) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1245), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1253), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d53) f618 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1255) (RestInside.out (n := 1255) f619 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1256) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1255), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1253), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d56) f619 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_31 code

theorem rest_l10446f_29 [Bindings] (code : CodeMap) :
    Rest (n := 1180) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 1178), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1176), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      253 0x104cb0 bytes_l10446f_29 b_l10446f_29 := by
  have f580 : InstrSpec 0x104cb0 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104cb0) (xorR32R32Effect 0x104cb0 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104cb0 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104cb0 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f581 : InstrSpec 0x104cb3 [0x66, 0x89, 0x5C, 0x24, 0x7E] (StorePre 0x104cb3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7e)) s (0x104cb3 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104cb3 5 3 (.sib 4 none 0 (.d8 0x7e)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104cb3 5 3 (.sib 4 none 0 (.d8 0x7e))).toInstrSpec (mov_m16_r16_effect_step 0x104cb3 3 (.sib 4 none 0 (.d8 0x7e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f582 : InstrSpec 0x104cb8 [0x0F, 0xB7, 0x9C, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x104cb8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x104cb8 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104cb8 8 3 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104cb8 8 3 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (movzx_r32_m16_effect_step 0x104cb8 3 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f583 : InstrSpec 0x104cc0 [0x41, 0x89, 0xDC] (fun s => s.RIP = 0x104cc0) (movR32R32Effect 0x104cc0 3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x104cc0 3 12 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104cc0 0x41 0xdc (by decide) (by decide)) pre_rip
  have f584 : InstrSpec 0x104cc3 [0x41, 0xC1, 0xEC, 0x02] (fun s => s.RIP = 0x104cc3) (shrR32Effect 0x104cc3 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x104cc3 4 12 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104cc3 0x41 0xec 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f585 : InstrSpec 0x104cc7 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104cc7) (xorR32R32Effect 0x104cc7 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104cc7 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104cc7 0x41 0xdc (by decide) (by decide)) pre_rip
  have f586 : InstrSpec 0x104cca [0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x104cca) (andR32Imm32Effect 0x104cca 7 12 0x2310)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104cca 7 12 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x104cca 0x41 0xe4 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f587 : InstrSpec 0x104cd1 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104cd1) (xorR32R32Effect 0x104cd1 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104cd1 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104cd1 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f588 : InstrSpec 0x104cd4 [0x41, 0xC1, 0xE4, 0x02] (fun s => s.RIP = 0x104cd4) (shlR32Effect 0x104cd4 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x104cd4 4 12 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104cd4 0x41 0xe4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f589 : InstrSpec 0x104cd8 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104cd8) (xorR32R32Effect 0x104cd8 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104cd8 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104cd8 0x41 0xdc (by decide) (by decide)) pre_rip
  have f590 : InstrSpec 0x104cdb [0x44, 0x89, 0xE3] (fun s => s.RIP = 0x104cdb) (movR32R32Effect 0x104cdb 3 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x104cdb 3 3 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x104cdb 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f591 : InstrSpec 0x104cde [0xD1, 0xEB] (fun s => s.RIP = 0x104cde) (shrR32Effect 0x104cde 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x104cde 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x104cde 0xeb (by decide) (by decide)) pre_rip
  have f592 : InstrSpec 0x104ce0 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104ce0) (xorR32R32Effect 0x104ce0 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ce0 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ce0 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f593 : InstrSpec 0x104ce3 [0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104ce3) (andR32Imm32Effect 0x104ce3 6 3 0x5050)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104ce3 6 3 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104ce3 0xe3 0x5050 (by decide) (by decide)) pre_rip
  have f594 : InstrSpec 0x104ce9 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104ce9) (xorR32R32Effect 0x104ce9 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ce9 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ce9 0x41 0xdc (by decide) (by decide)) pre_rip
  have f595 : InstrSpec 0x104cec [0x01, 0xDB] (fun s => s.RIP = 0x104cec) (addR32R32Effect 0x104cec 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104cec 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x104cec 0xdb (by decide)) pre_rip
  have f596 : InstrSpec 0x104cee [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104cee) (xorR32R32Effect 0x104cee 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104cee 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104cee 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f597 : InstrSpec 0x104cf1 [0x66, 0x89, 0x9C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x104cf1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x104cf1 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x104cf1 8 3 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104cf1 8 3 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m16_r16_effect_step 0x104cf1 3 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f598 : InstrSpec 0x104cf9 [0x0F, 0xB7, 0x9C, 0x24, 0x82, 0x00, 0x00, 0x00] (LoadPre 0x104cf9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x104cf9 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x104cf9 8 3 (.sib 4 none 0 (.d32 0x82)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104cf9 8 3 (.sib 4 none 0 (.d32 0x82))).toInstrSpec (movzx_r32_m16_effect_step 0x104cf9 3 (.sib 4 none 0 (.d32 0x82)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f599 : InstrSpec 0x104d01 [0x41, 0x89, 0xDC] (fun s => s.RIP = 0x104d01) (movR32R32Effect 0x104d01 3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x104d01 3 12 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104d01 0x41 0xdc (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1180) (RestInside.out (n := 1180) f580 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1181) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1180), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1176), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cb3) f580 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1182) (RestInside.exec (n := 1182) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1180), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1176), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cb8) f581 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1183) (RestInside.out (n := 1183) f582 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1184) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1183), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1176), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cc0) f582 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1185) (RestInside.out (n := 1185) f583 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1186) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1183), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1185), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cc3) f583 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1187) (RestInside.out (n := 1187) f584 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1188) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1183), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1187), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cc7) f584 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1189) (RestInside.out (n := 1189) f585 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1190) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1183), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1189), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cca) f585 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1191) (RestInside.out (n := 1191) f586 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1192) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1183), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1191), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cd1) f586 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1193) (RestInside.out (n := 1193) f587 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1194) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1193), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1191), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cd4) f587 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1195) (RestInside.out (n := 1195) f588 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1196) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1193), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1195), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cd8) f588 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1197) (RestInside.out (n := 1197) f589 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1198) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1193), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1197), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cdb) f589 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1199) (RestInside.out (n := 1199) f590 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1200) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1199), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1197), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cde) f590 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1201) (RestInside.out (n := 1201) f591 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1202) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1201), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1197), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ce0) f591 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1203) (RestInside.out (n := 1203) f592 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1204) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1203), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1197), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ce3) f592 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1205) (RestInside.out (n := 1205) f593 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1206) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1205), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1197), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ce9) f593 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1207) (RestInside.out (n := 1207) f594 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1208) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1205), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1207), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cec) f594 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1209) (RestInside.out (n := 1209) f595 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1210) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1209), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1207), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cee) f595 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1211) (RestInside.out (n := 1211) f596 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1212) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1211), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1207), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cf1) f596 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1213) (RestInside.exec (n := 1213) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1211), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1207), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cf9) f597 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1214) (RestInside.out (n := 1214) f598 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1215) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1214), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1207), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d01) f598 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1216) (RestInside.out (n := 1216) f599 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1217) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1214), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1216), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104d04) f599 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_30 code

theorem rest_l10446f_28 [Bindings] (code : CodeMap) :
    Rest (n := 1141) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 1139), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1135), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      273 0x104c67 bytes_l10446f_28 b_l10446f_28 := by
  have f560 : InstrSpec 0x104c67 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104c67) (xorR32R32Effect 0x104c67 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c67 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c67 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f561 : InstrSpec 0x104c6a [0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104c6a) (andR32Imm32Effect 0x104c6a 6 3 0x5050)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104c6a 6 3 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104c6a 0xe3 0x5050 (by decide) (by decide)) pre_rip
  have f562 : InstrSpec 0x104c70 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104c70) (xorR32R32Effect 0x104c70 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c70 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c70 0x41 0xdc (by decide) (by decide)) pre_rip
  have f563 : InstrSpec 0x104c73 [0x01, 0xDB] (fun s => s.RIP = 0x104c73) (addR32R32Effect 0x104c73 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104c73 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x104c73 0xdb (by decide)) pre_rip
  have f564 : InstrSpec 0x104c75 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104c75) (xorR32R32Effect 0x104c75 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c75 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c75 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f565 : InstrSpec 0x104c78 [0x66, 0x89, 0x5C, 0x24, 0x7C] (StorePre 0x104c78 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x104c78 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104c78 5 3 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104c78 5 3 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (mov_m16_r16_effect_step 0x104c78 3 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f566 : InstrSpec 0x104c7d [0x0F, 0xB7, 0x5C, 0x24, 0x7E] (LoadPre 0x104c7d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7e)) s (0x104c7d + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104c7d 5 3 (.sib 4 none 0 (.d8 0x7e)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104c7d 5 3 (.sib 4 none 0 (.d8 0x7e))).toInstrSpec (movzx_r32_m16_effect_step 0x104c7d 3 (.sib 4 none 0 (.d8 0x7e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f567 : InstrSpec 0x104c82 [0x41, 0x89, 0xDC] (fun s => s.RIP = 0x104c82) (movR32R32Effect 0x104c82 3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x104c82 3 12 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104c82 0x41 0xdc (by decide) (by decide)) pre_rip
  have f568 : InstrSpec 0x104c85 [0x41, 0xC1, 0xEC, 0x02] (fun s => s.RIP = 0x104c85) (shrR32Effect 0x104c85 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x104c85 4 12 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104c85 0x41 0xec 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f569 : InstrSpec 0x104c89 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104c89) (xorR32R32Effect 0x104c89 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c89 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c89 0x41 0xdc (by decide) (by decide)) pre_rip
  have f570 : InstrSpec 0x104c8c [0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x104c8c) (andR32Imm32Effect 0x104c8c 7 12 0x2310)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104c8c 7 12 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x104c8c 0x41 0xe4 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f571 : InstrSpec 0x104c93 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104c93) (xorR32R32Effect 0x104c93 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c93 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c93 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f572 : InstrSpec 0x104c96 [0x41, 0xC1, 0xE4, 0x02] (fun s => s.RIP = 0x104c96) (shlR32Effect 0x104c96 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x104c96 4 12 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104c96 0x41 0xe4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f573 : InstrSpec 0x104c9a [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104c9a) (xorR32R32Effect 0x104c9a 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c9a 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c9a 0x41 0xdc (by decide) (by decide)) pre_rip
  have f574 : InstrSpec 0x104c9d [0x44, 0x89, 0xE3] (fun s => s.RIP = 0x104c9d) (movR32R32Effect 0x104c9d 3 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x104c9d 3 3 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x104c9d 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f575 : InstrSpec 0x104ca0 [0xD1, 0xEB] (fun s => s.RIP = 0x104ca0) (shrR32Effect 0x104ca0 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x104ca0 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x104ca0 0xeb (by decide) (by decide)) pre_rip
  have f576 : InstrSpec 0x104ca2 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104ca2) (xorR32R32Effect 0x104ca2 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ca2 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ca2 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f577 : InstrSpec 0x104ca5 [0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104ca5) (andR32Imm32Effect 0x104ca5 6 3 0x5050)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104ca5 6 3 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104ca5 0xe3 0x5050 (by decide) (by decide)) pre_rip
  have f578 : InstrSpec 0x104cab [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104cab) (xorR32R32Effect 0x104cab 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104cab 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104cab 0x41 0xdc (by decide) (by decide)) pre_rip
  have f579 : InstrSpec 0x104cae [0x01, 0xDB] (fun s => s.RIP = 0x104cae) (addR32R32Effect 0x104cae 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104cae 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x104cae 0xdb (by decide)) pre_rip
  refine Rest.ofInside (n := 1141) (RestInside.out (n := 1141) f560 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1142) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1141), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1135), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c6a) f560 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1143) (RestInside.out (n := 1143) f561 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1144) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1143), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1135), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c70) f561 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1145) (RestInside.out (n := 1145) f562 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1146) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1143), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1145), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c73) f562 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1147) (RestInside.out (n := 1147) f563 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1148) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1147), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1145), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c75) f563 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1149) (RestInside.out (n := 1149) f564 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1150) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1149), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1145), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c78) f564 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1151) (RestInside.exec (n := 1151) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1149), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1145), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c7d) f565 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1152) (RestInside.out (n := 1152) f566 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1153) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1152), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1145), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c82) f566 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1154) (RestInside.out (n := 1154) f567 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1155) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1152), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1154), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c85) f567 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1156) (RestInside.out (n := 1156) f568 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1157) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1152), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1156), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c89) f568 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1158) (RestInside.out (n := 1158) f569 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1159) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1152), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1158), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c8c) f569 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1160) (RestInside.out (n := 1160) f570 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1161) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1152), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1160), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c93) f570 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1162) (RestInside.out (n := 1162) f571 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1163) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1162), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1160), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c96) f571 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1164) (RestInside.out (n := 1164) f572 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1165) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1162), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1164), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c9a) f572 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1166) (RestInside.out (n := 1166) f573 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1167) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1162), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1166), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c9d) f573 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1168) (RestInside.out (n := 1168) f574 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1169) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1168), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1166), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ca0) f574 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1170) (RestInside.out (n := 1170) f575 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1171) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1170), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1166), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ca2) f575 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1172) (RestInside.out (n := 1172) f576 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1173) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1172), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1166), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ca5) f576 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1174) (RestInside.out (n := 1174) f577 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1175) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1174), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1166), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cab) f577 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1176) (RestInside.out (n := 1176) f578 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1177) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1174), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1176), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cae) f578 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1178) (RestInside.out (n := 1178) f579 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1179) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1178), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1176), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104cb0) f579 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_29 code

theorem rest_l10446f_27 [Bindings] (code : CodeMap) :
    Rest (n := 1102) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 1100), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1098), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]
      293 0x104c20 bytes_l10446f_27 b_l10446f_27 := by
  have f540 : InstrSpec 0x104c20 [0x41, 0xC1, 0xE4, 0x02] (fun s => s.RIP = 0x104c20) (shlR32Effect 0x104c20 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x104c20 4 12 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104c20 0x41 0xe4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f541 : InstrSpec 0x104c24 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104c24) (xorR32R32Effect 0x104c24 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c24 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c24 0x41 0xdc (by decide) (by decide)) pre_rip
  have f542 : InstrSpec 0x104c27 [0x44, 0x89, 0xE3] (fun s => s.RIP = 0x104c27) (movR32R32Effect 0x104c27 3 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x104c27 3 3 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x104c27 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f543 : InstrSpec 0x104c2a [0xD1, 0xEB] (fun s => s.RIP = 0x104c2a) (shrR32Effect 0x104c2a 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x104c2a 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x104c2a 0xeb (by decide) (by decide)) pre_rip
  have f544 : InstrSpec 0x104c2c [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104c2c) (xorR32R32Effect 0x104c2c 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c2c 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c2c 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f545 : InstrSpec 0x104c2f [0x81, 0xE3, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104c2f) (andR32Imm32Effect 0x104c2f 6 3 0x5050)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104c2f 6 3 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x104c2f 0xe3 0x5050 (by decide) (by decide)) pre_rip
  have f546 : InstrSpec 0x104c35 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104c35) (xorR32R32Effect 0x104c35 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c35 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c35 0x41 0xdc (by decide) (by decide)) pre_rip
  have f547 : InstrSpec 0x104c38 [0x01, 0xDB] (fun s => s.RIP = 0x104c38) (addR32R32Effect 0x104c38 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104c38 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x104c38 0xdb (by decide)) pre_rip
  have f548 : InstrSpec 0x104c3a [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104c3a) (xorR32R32Effect 0x104c3a 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c3a 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c3a 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f549 : InstrSpec 0x104c3d [0x66, 0x89, 0x5C, 0x24, 0x7A] (StorePre 0x104c3d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7a)) s (0x104c3d + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104c3d 5 3 (.sib 4 none 0 (.d8 0x7a)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104c3d 5 3 (.sib 4 none 0 (.d8 0x7a))).toInstrSpec (mov_m16_r16_effect_step 0x104c3d 3 (.sib 4 none 0 (.d8 0x7a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f550 : InstrSpec 0x104c42 [0x0F, 0xB7, 0x5C, 0x24, 0x7C] (LoadPre 0x104c42 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x104c42 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104c42 5 3 (.sib 4 none 0 (.d8 0x7c)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104c42 5 3 (.sib 4 none 0 (.d8 0x7c))).toInstrSpec (movzx_r32_m16_effect_step 0x104c42 3 (.sib 4 none 0 (.d8 0x7c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f551 : InstrSpec 0x104c47 [0x41, 0x89, 0xDC] (fun s => s.RIP = 0x104c47) (movR32R32Effect 0x104c47 3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x104c47 3 12 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104c47 0x41 0xdc (by decide) (by decide)) pre_rip
  have f552 : InstrSpec 0x104c4a [0x41, 0xC1, 0xEC, 0x02] (fun s => s.RIP = 0x104c4a) (shrR32Effect 0x104c4a 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x104c4a 4 12 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104c4a 0x41 0xec 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f553 : InstrSpec 0x104c4e [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104c4e) (xorR32R32Effect 0x104c4e 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c4e 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c4e 0x41 0xdc (by decide) (by decide)) pre_rip
  have f554 : InstrSpec 0x104c51 [0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x104c51) (andR32Imm32Effect 0x104c51 7 12 0x2310)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104c51 7 12 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x104c51 0x41 0xe4 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f555 : InstrSpec 0x104c58 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104c58) (xorR32R32Effect 0x104c58 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c58 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c58 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f556 : InstrSpec 0x104c5b [0x41, 0xC1, 0xE4, 0x02] (fun s => s.RIP = 0x104c5b) (shlR32Effect 0x104c5b 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x104c5b 4 12 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104c5b 0x41 0xe4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f557 : InstrSpec 0x104c5f [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104c5f) (xorR32R32Effect 0x104c5f 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c5f 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c5f 0x41 0xdc (by decide) (by decide)) pre_rip
  have f558 : InstrSpec 0x104c62 [0x44, 0x89, 0xE3] (fun s => s.RIP = 0x104c62) (movR32R32Effect 0x104c62 3 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x104c62 3 3 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x104c62 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f559 : InstrSpec 0x104c65 [0xD1, 0xEB] (fun s => s.RIP = 0x104c65) (shrR32Effect 0x104c65 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x104c65 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x104c65 0xeb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1102) (RestInside.out (n := 1102) f540 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1103) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1100), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1102), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c24) f540 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1104) (RestInside.out (n := 1104) f541 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1105) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1100), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1104), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c27) f541 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1106) (RestInside.out (n := 1106) f542 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1107) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1106), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1104), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c2a) f542 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1108) (RestInside.out (n := 1108) f543 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1109) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1108), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1104), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c2c) f543 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1110) (RestInside.out (n := 1110) f544 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1111) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1110), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1104), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c2f) f544 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1112) (RestInside.out (n := 1112) f545 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1113) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1112), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1104), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c35) f545 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1114) (RestInside.out (n := 1114) f546 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1115) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1112), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1114), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c38) f546 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1116) (RestInside.out (n := 1116) f547 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1117) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1116), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1114), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c3a) f547 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1118) (RestInside.out (n := 1118) f548 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1119) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1118), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1114), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c3d) f548 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1120) (RestInside.exec (n := 1120) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1118), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1114), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c42) f549 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1121) (RestInside.out (n := 1121) f550 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1122) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1121), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1114), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c47) f550 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1123) (RestInside.out (n := 1123) f551 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1124) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1121), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1123), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c4a) f551 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1125) (RestInside.out (n := 1125) f552 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1126) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1121), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1125), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c4e) f552 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1127) (RestInside.out (n := 1127) f553 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1128) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1121), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1127), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c51) f553 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1129) (RestInside.out (n := 1129) f554 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1130) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1121), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1129), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c58) f554 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1131) (RestInside.out (n := 1131) f555 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1132) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1131), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1129), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c5b) f555 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1133) (RestInside.out (n := 1133) f556 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1134) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1131), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1133), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c5f) f556 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1135) (RestInside.out (n := 1135) f557 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1136) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1131), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1135), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c62) f557 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1137) (RestInside.out (n := 1137) f558 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1138) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1137), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1135), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c65) f558 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1139) (RestInside.out (n := 1139) f559 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1140) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1139), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1135), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c67) f559 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_28 code

theorem rest_l10446f_26 [Bindings] (code : CodeMap) :
    Rest (n := 1062) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 1060), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]
      313 0x104bd3 bytes_l10446f_26 b_l10446f_26 := by
  have f520 : InstrSpec 0x104bd3 [0x41, 0x89, 0xDC] (fun s => s.RIP = 0x104bd3) (movR32R32Effect 0x104bd3 3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x104bd3 3 12 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104bd3 0x41 0xdc (by decide) (by decide)) pre_rip
  have f521 : InstrSpec 0x104bd6 [0x41, 0xC1, 0xEC, 0x02] (fun s => s.RIP = 0x104bd6) (shrR32Effect 0x104bd6 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x104bd6 4 12 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104bd6 0x41 0xec 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f522 : InstrSpec 0x104bda [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104bda) (xorR32R32Effect 0x104bda 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104bda 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104bda 0x41 0xdc (by decide) (by decide)) pre_rip
  have f523 : InstrSpec 0x104bdd [0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x104bdd) (andR32Imm32Effect 0x104bdd 7 12 0x2310)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104bdd 7 12 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x104bdd 0x41 0xe4 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f524 : InstrSpec 0x104be4 [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104be4) (xorR32R32Effect 0x104be4 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104be4 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104be4 0x44 0xe3 (by decide) (by decide)) pre_rip
  have f525 : InstrSpec 0x104be7 [0x41, 0xC1, 0xE4, 0x02] (fun s => s.RIP = 0x104be7) (shlR32Effect 0x104be7 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shlR32Effect_footprint 0x104be7 4 12 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104be7 0x41 0xe4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f526 : InstrSpec 0x104beb [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104beb) (xorR32R32Effect 0x104beb 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104beb 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104beb 0x41 0xdc (by decide) (by decide)) pre_rip
  have f527 : InstrSpec 0x104bee [0x45, 0x89, 0xE7] (fun s => s.RIP = 0x104bee) (movR32R32Effect 0x104bee 3 15 12)
      [.gpr 12] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x104bee 3 15 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x104bee 0x45 0xe7 (by decide) (by decide)) pre_rip
  have f528 : InstrSpec 0x104bf1 [0x41, 0xD1, 0xEF] (fun s => s.RIP = 0x104bf1) (shrR32Effect 0x104bf1 3 15 1)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR32Effect_footprint 0x104bf1 3 15 1).toInstrSpec (shr_r32_one_rex_effect_step 0x104bf1 0x41 0xef (by decide) (by decide) (by decide)) pre_rip
  have f529 : InstrSpec 0x104bf4 [0x45, 0x31, 0xE7] (fun s => s.RIP = 0x104bf4) (xorR32R32Effect 0x104bf4 3 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104bf4 3 15 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104bf4 0x45 0xe7 (by decide) (by decide)) pre_rip
  have f530 : InstrSpec 0x104bf7 [0x41, 0x81, 0xE7, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104bf7) (andR32Imm32Effect 0x104bf7 7 15 0x5050)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104bf7 7 15 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104bf7 0x41 0xe7 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f531 : InstrSpec 0x104bfe [0x45, 0x31, 0xFC] (fun s => s.RIP = 0x104bfe) (xorR32R32Effect 0x104bfe 3 12 15)
      [.gpr 12, .gpr 15] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104bfe 3 12 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x104bfe 0x45 0xfc (by decide) (by decide)) pre_rip
  have f532 : InstrSpec 0x104c01 [0x45, 0x01, 0xFF] (fun s => s.RIP = 0x104c01) (addR32R32Effect 0x104c01 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104c01 3 15 15).toInstrSpec (add_r32_r32_rex_effect_step 0x104c01 0x45 0xff (by decide) (by decide)) pre_rip
  have f533 : InstrSpec 0x104c04 [0x45, 0x31, 0xE7] (fun s => s.RIP = 0x104c04) (xorR32R32Effect 0x104c04 3 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c04 3 15 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c04 0x45 0xe7 (by decide) (by decide)) pre_rip
  have f534 : InstrSpec 0x104c07 [0x0F, 0xB7, 0x5C, 0x24, 0x7A] (LoadPre 0x104c07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7a)) s (0x104c07 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104c07 5 3 (.sib 4 none 0 (.d8 0x7a)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104c07 5 3 (.sib 4 none 0 (.d8 0x7a))).toInstrSpec (movzx_r32_m16_effect_step 0x104c07 3 (.sib 4 none 0 (.d8 0x7a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f535 : InstrSpec 0x104c0c [0x41, 0x89, 0xDC] (fun s => s.RIP = 0x104c0c) (movR32R32Effect 0x104c0c 3 12 3)
      [.gpr 3] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x104c0c 3 12 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104c0c 0x41 0xdc (by decide) (by decide)) pre_rip
  have f536 : InstrSpec 0x104c0f [0x41, 0xC1, 0xEC, 0x02] (fun s => s.RIP = 0x104c0f) (shrR32Effect 0x104c0f 4 12 2)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (shrR32Effect_footprint 0x104c0f 4 12 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104c0f 0x41 0xec 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f537 : InstrSpec 0x104c13 [0x41, 0x31, 0xDC] (fun s => s.RIP = 0x104c13) (xorR32R32Effect 0x104c13 3 12 3)
      [.gpr 12, .gpr 3] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c13 3 12 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c13 0x41 0xdc (by decide) (by decide)) pre_rip
  have f538 : InstrSpec 0x104c16 [0x41, 0x81, 0xE4, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x104c16) (andR32Imm32Effect 0x104c16 7 12 0x2310)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104c16 7 12 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x104c16 0x41 0xe4 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f539 : InstrSpec 0x104c1d [0x44, 0x31, 0xE3] (fun s => s.RIP = 0x104c1d) (xorR32R32Effect 0x104c1d 3 3 12)
      [.gpr 3, .gpr 12] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104c1d 3 3 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x104c1d 0x44 0xe3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 1062) (RestInside.out (n := 1062) f520 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1063) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1060), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1062), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bd6) f520 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1064) (RestInside.out (n := 1064) f521 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1065) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1060), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1064), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bda) f521 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1066) (RestInside.out (n := 1066) f522 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1067) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1060), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1066), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bdd) f522 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1068) (RestInside.out (n := 1068) f523 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1069) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1060), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1068), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104be4) f523 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1070) (RestInside.out (n := 1070) f524 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1071) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1070), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1068), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104be7) f524 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1072) (RestInside.out (n := 1072) f525 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1073) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1070), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1072), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104beb) f525 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1074) (RestInside.out (n := 1074) f526 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1075) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1070), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1074), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bee) f526 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1076) (RestInside.out (n := 1076) f527 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1077) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1070), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1074), (14, 1041), (15, 1076), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bf1) f527 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1078) (RestInside.out (n := 1078) f528 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1079) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1070), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1074), (14, 1041), (15, 1078), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bf4) f528 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1080) (RestInside.out (n := 1080) f529 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1081) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1070), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1074), (14, 1041), (15, 1080), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bf7) f529 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1082) (RestInside.out (n := 1082) f530 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1083) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1070), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1074), (14, 1041), (15, 1082), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bfe) f530 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1084) (RestInside.out (n := 1084) f531 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1085) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1070), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1084), (14, 1041), (15, 1082), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c01) f531 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1086) (RestInside.out (n := 1086) f532 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1087) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1070), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1084), (14, 1041), (15, 1086), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c04) f532 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1088) (RestInside.out (n := 1088) f533 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1089) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1070), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1084), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c07) f533 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1090) (RestInside.out (n := 1090) f534 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1091) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1090), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1084), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c0c) f534 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1092) (RestInside.out (n := 1092) f535 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1093) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1090), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1092), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c0f) f535 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1094) (RestInside.out (n := 1094) f536 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1095) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1090), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1094), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c13) f536 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1096) (RestInside.out (n := 1096) f537 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1097) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1090), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1096), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c16) f537 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1098) (RestInside.out (n := 1098) f538 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1099) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1090), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1098), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c1d) f538 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1100) (RestInside.out (n := 1100) f539 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1101) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1100), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (12, 1098), (14, 1041), (15, 1088), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104c20) f539 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_27 code

theorem rest_l10446f_25 [Bindings] (code : CodeMap) :
    Rest (n := 1023) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 1021), (4, 4), (5, 1019), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]
      333 0x104b83 bytes_l10446f_25 b_l10446f_25 := by
  have f500 : InstrSpec 0x104b83 [0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x104b83) (shlR32Effect 0x104b83 3 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR32Effect_footprint 0x104b83 3 5 2).toInstrSpec (shl_r32_imm8_effect_step 0x104b83 0xe5 0x2 (by decide) (by decide)) pre_rip
  have f501 : InstrSpec 0x104b86 [0x31, 0xDD] (fun s => s.RIP = 0x104b86) (xorR32R32Effect 0x104b86 2 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b86 2 5 3).toInstrSpec (xor_r32_r32_effect_step 0x104b86 0xdd (by decide)) pre_rip
  have f502 : InstrSpec 0x104b88 [0x0F, 0xB7, 0x5C, 0x24, 0x74] (LoadPre 0x104b88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x104b88 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104b88 5 3 (.sib 4 none 0 (.d8 0x74)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104b88 5 3 (.sib 4 none 0 (.d8 0x74))).toInstrSpec (movzx_r32_m16_effect_step 0x104b88 3 (.sib 4 none 0 (.d8 0x74)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f503 : InstrSpec 0x104b8d [0x41, 0x89, 0xDE] (fun s => s.RIP = 0x104b8d) (movR32R32Effect 0x104b8d 3 14 3)
      [.gpr 3] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x104b8d 3 14 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104b8d 0x41 0xde (by decide) (by decide)) pre_rip
  have f504 : InstrSpec 0x104b90 [0x41, 0xC1, 0xEE, 0x02] (fun s => s.RIP = 0x104b90) (shrR32Effect 0x104b90 4 14 2)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR32Effect_footprint 0x104b90 4 14 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104b90 0x41 0xee 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f505 : InstrSpec 0x104b94 [0x41, 0x31, 0xDE] (fun s => s.RIP = 0x104b94) (xorR32R32Effect 0x104b94 3 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b94 3 14 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104b94 0x41 0xde (by decide) (by decide)) pre_rip
  have f506 : InstrSpec 0x104b97 [0x41, 0x81, 0xE6, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104b97) (andR32Imm32Effect 0x104b97 7 14 0x3030)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104b97 7 14 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x104b97 0x41 0xe6 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f507 : InstrSpec 0x104b9e [0x44, 0x31, 0xF3] (fun s => s.RIP = 0x104b9e) (xorR32R32Effect 0x104b9e 3 3 14)
      [.gpr 3, .gpr 14] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b9e 3 3 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x104b9e 0x44 0xf3 (by decide) (by decide)) pre_rip
  have f508 : InstrSpec 0x104ba1 [0x41, 0xC1, 0xE6, 0x02] (fun s => s.RIP = 0x104ba1) (shlR32Effect 0x104ba1 4 14 2)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shlR32Effect_footprint 0x104ba1 4 14 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104ba1 0x41 0xe6 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f509 : InstrSpec 0x104ba5 [0x41, 0x31, 0xDE] (fun s => s.RIP = 0x104ba5) (xorR32R32Effect 0x104ba5 3 14 3)
      [.gpr 14, .gpr 3] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ba5 3 14 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ba5 0x41 0xde (by decide) (by decide)) pre_rip
  have f510 : InstrSpec 0x104ba8 [0x0F, 0xB7, 0x5C, 0x24, 0x76] (LoadPre 0x104ba8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x104ba8 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104ba8 5 3 (.sib 4 none 0 (.d8 0x76)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104ba8 5 3 (.sib 4 none 0 (.d8 0x76))).toInstrSpec (movzx_r32_m16_effect_step 0x104ba8 3 (.sib 4 none 0 (.d8 0x76)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f511 : InstrSpec 0x104bad [0x41, 0x89, 0xDF] (fun s => s.RIP = 0x104bad) (movR32R32Effect 0x104bad 3 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x104bad 3 15 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104bad 0x41 0xdf (by decide) (by decide)) pre_rip
  have f512 : InstrSpec 0x104bb0 [0x41, 0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x104bb0) (shrR32Effect 0x104bb0 4 15 2)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR32Effect_footprint 0x104bb0 4 15 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104bb0 0x41 0xef 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f513 : InstrSpec 0x104bb4 [0x41, 0x31, 0xDF] (fun s => s.RIP = 0x104bb4) (xorR32R32Effect 0x104bb4 3 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104bb4 3 15 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104bb4 0x41 0xdf (by decide) (by decide)) pre_rip
  have f514 : InstrSpec 0x104bb7 [0x41, 0x81, 0xE7, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104bb7) (andR32Imm32Effect 0x104bb7 7 15 0x3030)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104bb7 7 15 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x104bb7 0x41 0xe7 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f515 : InstrSpec 0x104bbe [0x44, 0x31, 0xFB] (fun s => s.RIP = 0x104bbe) (xorR32R32Effect 0x104bbe 3 3 15)
      [.gpr 3, .gpr 15] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104bbe 3 3 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x104bbe 0x44 0xfb (by decide) (by decide)) pre_rip
  have f516 : InstrSpec 0x104bc1 [0x41, 0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x104bc1) (shlR32Effect 0x104bc1 4 15 2)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR32Effect_footprint 0x104bc1 4 15 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104bc1 0x41 0xe7 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f517 : InstrSpec 0x104bc5 [0x41, 0x31, 0xDF] (fun s => s.RIP = 0x104bc5) (xorR32R32Effect 0x104bc5 3 15 3)
      [.gpr 15, .gpr 3] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104bc5 3 15 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104bc5 0x41 0xdf (by decide) (by decide)) pre_rip
  have f518 : InstrSpec 0x104bc8 [0x66, 0x44, 0x89, 0x7C, 0x24, 0x76] (StorePre 0x104bc8 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x104bc8 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104bc8 6 15 (.sib 4 none 0 (.d8 0x76)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104bc8 6 15 (.sib 4 none 0 (.d8 0x76))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104bc8 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x76)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f519 : InstrSpec 0x104bce [0x0F, 0xB7, 0x5C, 0x24, 0x78] (LoadPre 0x104bce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x104bce + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104bce 5 3 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104bce 5 3 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (movzx_r32_m16_effect_step 0x104bce 3 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 1023) (RestInside.out (n := 1023) f500 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1024) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1021), (4, 4), (5, 1023), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b86) f500 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1025) (RestInside.out (n := 1025) f501 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1026) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1021), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b88) f501 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1027) (RestInside.out (n := 1027) f502 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1028) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1027), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b8d) f502 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1029) (RestInside.out (n := 1029) f503 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1030) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1027), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1029), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b90) f503 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1031) (RestInside.out (n := 1031) f504 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1032) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1027), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1031), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b94) f504 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1033) (RestInside.out (n := 1033) f505 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1034) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1027), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1033), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b97) f505 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1035) (RestInside.out (n := 1035) f506 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1036) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1027), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1035), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b9e) f506 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1037) (RestInside.out (n := 1037) f507 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1038) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1037), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1035), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ba1) f507 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1039) (RestInside.out (n := 1039) f508 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1040) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1037), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1039), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ba5) f508 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1041) (RestInside.out (n := 1041) f509 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1042) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1037), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ba8) f509 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1043) (RestInside.out (n := 1043) f510 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1044) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1043), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bad) f510 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1045) (RestInside.out (n := 1045) f511 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1046) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1043), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (15, 1045), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bb0) f511 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1047) (RestInside.out (n := 1047) f512 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1048) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1043), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (15, 1047), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bb4) f512 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1049) (RestInside.out (n := 1049) f513 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1050) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1043), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (15, 1049), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bb7) f513 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1051) (RestInside.out (n := 1051) f514 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1052) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1043), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (15, 1051), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bbe) f514 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1053) (RestInside.out (n := 1053) f515 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1054) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1053), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (15, 1051), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bc1) f515 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1055) (RestInside.out (n := 1055) f516 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1056) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1053), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (15, 1055), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bc5) f516 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1057) (RestInside.out (n := 1057) f517 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1058) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1053), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bc8) f517 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1059) (RestInside.exec (n := 1059) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1053), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bce) f518 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1060) (RestInside.out (n := 1060) f519 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1061) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1060), (4, 4), (5, 1025), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (14, 1041), (15, 1057), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104bd3) f519 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_26 code

theorem rest_l10446f_24 [Bindings] (code : CodeMap) :
    Rest (n := 985) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 977), (4, 4), (5, 983), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]
      353 0x104b3f bytes_l10446f_24 b_l10446f_24 := by
  have f480 : InstrSpec 0x104b3f [0x81, 0xE5, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104b3f) (andR32Imm32Effect 0x104b3f 6 5 0x3030)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104b3f 6 5 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x104b3f 0xe5 0x3030 (by decide) (by decide)) pre_rip
  have f481 : InstrSpec 0x104b45 [0x31, 0xEB] (fun s => s.RIP = 0x104b45) (xorR32R32Effect 0x104b45 2 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b45 2 3 5).toInstrSpec (xor_r32_r32_effect_step 0x104b45 0xeb (by decide)) pre_rip
  have f482 : InstrSpec 0x104b47 [0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x104b47) (shlR32Effect 0x104b47 3 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR32Effect_footprint 0x104b47 3 5 2).toInstrSpec (shl_r32_imm8_effect_step 0x104b47 0xe5 0x2 (by decide) (by decide)) pre_rip
  have f483 : InstrSpec 0x104b4a [0x31, 0xDD] (fun s => s.RIP = 0x104b4a) (xorR32R32Effect 0x104b4a 2 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b4a 2 5 3).toInstrSpec (xor_r32_r32_effect_step 0x104b4a 0xdd (by decide)) pre_rip
  have f484 : InstrSpec 0x104b4c [0x66, 0x89, 0x6C, 0x24, 0x6E] (StorePre 0x104b4c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x104b4c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104b4c 5 5 (.sib 4 none 0 (.d8 0x6e)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104b4c 5 5 (.sib 4 none 0 (.d8 0x6e))).toInstrSpec (mov_m16_r16_effect_step 0x104b4c 5 (.sib 4 none 0 (.d8 0x6e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f485 : InstrSpec 0x104b51 [0x0F, 0xB7, 0x5C, 0x24, 0x70] (LoadPre 0x104b51 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x104b51 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104b51 5 3 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104b51 5 3 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (movzx_r32_m16_effect_step 0x104b51 3 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f486 : InstrSpec 0x104b56 [0x89, 0xDD] (fun s => s.RIP = 0x104b56) (movR32R32Effect 0x104b56 2 5 3)
      [.gpr 3] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x104b56 2 5 3).toInstrSpec (mov_r32_r32_effect_step 0x104b56 0xdd (by decide)) pre_rip
  have f487 : InstrSpec 0x104b58 [0xC1, 0xED, 0x02] (fun s => s.RIP = 0x104b58) (shrR32Effect 0x104b58 3 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR32Effect_footprint 0x104b58 3 5 2).toInstrSpec (shr_r32_imm8_effect_step 0x104b58 0xed 0x2 (by decide) (by decide)) pre_rip
  have f488 : InstrSpec 0x104b5b [0x31, 0xDD] (fun s => s.RIP = 0x104b5b) (xorR32R32Effect 0x104b5b 2 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b5b 2 5 3).toInstrSpec (xor_r32_r32_effect_step 0x104b5b 0xdd (by decide)) pre_rip
  have f489 : InstrSpec 0x104b5d [0x81, 0xE5, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104b5d) (andR32Imm32Effect 0x104b5d 6 5 0x3030)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104b5d 6 5 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x104b5d 0xe5 0x3030 (by decide) (by decide)) pre_rip
  have f490 : InstrSpec 0x104b63 [0x31, 0xEB] (fun s => s.RIP = 0x104b63) (xorR32R32Effect 0x104b63 2 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b63 2 3 5).toInstrSpec (xor_r32_r32_effect_step 0x104b63 0xeb (by decide)) pre_rip
  have f491 : InstrSpec 0x104b65 [0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x104b65) (shlR32Effect 0x104b65 3 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR32Effect_footprint 0x104b65 3 5 2).toInstrSpec (shl_r32_imm8_effect_step 0x104b65 0xe5 0x2 (by decide) (by decide)) pre_rip
  have f492 : InstrSpec 0x104b68 [0x31, 0xDD] (fun s => s.RIP = 0x104b68) (xorR32R32Effect 0x104b68 2 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b68 2 5 3).toInstrSpec (xor_r32_r32_effect_step 0x104b68 0xdd (by decide)) pre_rip
  have f493 : InstrSpec 0x104b6a [0x66, 0x89, 0x6C, 0x24, 0x70] (StorePre 0x104b6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x104b6a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104b6a 5 5 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104b6a 5 5 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m16_r16_effect_step 0x104b6a 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f494 : InstrSpec 0x104b6f [0x0F, 0xB7, 0x5C, 0x24, 0x72] (LoadPre 0x104b6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x104b6f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104b6f 5 3 (.sib 4 none 0 (.d8 0x72)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104b6f 5 3 (.sib 4 none 0 (.d8 0x72))).toInstrSpec (movzx_r32_m16_effect_step 0x104b6f 3 (.sib 4 none 0 (.d8 0x72)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f495 : InstrSpec 0x104b74 [0x89, 0xDD] (fun s => s.RIP = 0x104b74) (movR32R32Effect 0x104b74 2 5 3)
      [.gpr 3] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x104b74 2 5 3).toInstrSpec (mov_r32_r32_effect_step 0x104b74 0xdd (by decide)) pre_rip
  have f496 : InstrSpec 0x104b76 [0xC1, 0xED, 0x02] (fun s => s.RIP = 0x104b76) (shrR32Effect 0x104b76 3 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR32Effect_footprint 0x104b76 3 5 2).toInstrSpec (shr_r32_imm8_effect_step 0x104b76 0xed 0x2 (by decide) (by decide)) pre_rip
  have f497 : InstrSpec 0x104b79 [0x31, 0xDD] (fun s => s.RIP = 0x104b79) (xorR32R32Effect 0x104b79 2 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b79 2 5 3).toInstrSpec (xor_r32_r32_effect_step 0x104b79 0xdd (by decide)) pre_rip
  have f498 : InstrSpec 0x104b7b [0x81, 0xE5, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104b7b) (andR32Imm32Effect 0x104b7b 6 5 0x3030)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104b7b 6 5 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x104b7b 0xe5 0x3030 (by decide) (by decide)) pre_rip
  have f499 : InstrSpec 0x104b81 [0x31, 0xEB] (fun s => s.RIP = 0x104b81) (xorR32R32Effect 0x104b81 2 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b81 2 3 5).toInstrSpec (xor_r32_r32_effect_step 0x104b81 0xeb (by decide)) pre_rip
  refine Rest.ofInside (n := 985) (RestInside.out (n := 985) f480 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 986) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 977), (4, 4), (5, 985), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b45) f480 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 987) (RestInside.out (n := 987) f481 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 988) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 987), (4, 4), (5, 985), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b47) f481 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 989) (RestInside.out (n := 989) f482 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 990) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 987), (4, 4), (5, 989), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b4a) f482 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 991) (RestInside.out (n := 991) f483 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 992) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 987), (4, 4), (5, 991), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b4c) f483 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 993) (RestInside.exec (n := 993) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 987), (4, 4), (5, 991), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b51) f484 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 994) (RestInside.out (n := 994) f485 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 995) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 994), (4, 4), (5, 991), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b56) f485 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 996) (RestInside.out (n := 996) f486 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 997) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 994), (4, 4), (5, 996), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b58) f486 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 998) (RestInside.out (n := 998) f487 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 999) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 994), (4, 4), (5, 998), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b5b) f487 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1000) (RestInside.out (n := 1000) f488 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1001) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 994), (4, 4), (5, 1000), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b5d) f488 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1002) (RestInside.out (n := 1002) f489 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1003) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 994), (4, 4), (5, 1002), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b63) f489 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1004) (RestInside.out (n := 1004) f490 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1005) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1004), (4, 4), (5, 1002), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b65) f490 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1006) (RestInside.out (n := 1006) f491 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1007) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1004), (4, 4), (5, 1006), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b68) f491 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1008) (RestInside.out (n := 1008) f492 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1009) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1004), (4, 4), (5, 1008), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b6a) f492 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1010) (RestInside.exec (n := 1010) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1004), (4, 4), (5, 1008), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b6f) f493 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 1011) (RestInside.out (n := 1011) f494 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1012) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1011), (4, 4), (5, 1008), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b74) f494 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1013) (RestInside.out (n := 1013) f495 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1014) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1011), (4, 4), (5, 1013), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b76) f495 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1015) (RestInside.out (n := 1015) f496 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1016) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1011), (4, 4), (5, 1015), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b79) f496 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1017) (RestInside.out (n := 1017) f497 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1018) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1011), (4, 4), (5, 1017), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b7b) f497 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1019) (RestInside.out (n := 1019) f498 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1020) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1011), (4, 4), (5, 1019), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b81) f498 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 1021) (RestInside.out (n := 1021) f499 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 1022) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 1021), (4, 4), (5, 1019), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b83) f499 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_25 code

theorem rest_l10446f_23 [Bindings] (code : CodeMap) :
    Rest (n := 946) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (3, 944), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 938), (22, 22), (39, 39), (50, 50), (51, 51)]
      373 0x104afa bytes_l10446f_23 b_l10446f_23 := by
  have f460 : InstrSpec 0x104afa [0x41, 0x89, 0xDB] (fun s => s.RIP = 0x104afa) (movR32R32Effect 0x104afa 3 11 3)
      [.gpr 3] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x104afa 3 11 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x104afa 0x41 0xdb (by decide) (by decide)) pre_rip
  have f461 : InstrSpec 0x104afd [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x104afd) (shrR32Effect 0x104afd 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x104afd 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104afd 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f462 : InstrSpec 0x104b01 [0x41, 0x31, 0xDB] (fun s => s.RIP = 0x104b01) (xorR32R32Effect 0x104b01 3 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b01 3 11 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104b01 0x41 0xdb (by decide) (by decide)) pre_rip
  have f463 : InstrSpec 0x104b04 [0x41, 0x81, 0xE3, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104b04) (andR32Imm32Effect 0x104b04 7 11 0x3030)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104b04 7 11 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x104b04 0x41 0xe3 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f464 : InstrSpec 0x104b0b [0x44, 0x31, 0xDB] (fun s => s.RIP = 0x104b0b) (xorR32R32Effect 0x104b0b 3 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b0b 3 3 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104b0b 0x44 0xdb (by decide) (by decide)) pre_rip
  have f465 : InstrSpec 0x104b0e [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x104b0e) (shlR32Effect 0x104b0e 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x104b0e 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104b0e 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f466 : InstrSpec 0x104b12 [0x41, 0x31, 0xDB] (fun s => s.RIP = 0x104b12) (xorR32R32Effect 0x104b12 3 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b12 3 11 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x104b12 0x41 0xdb (by decide) (by decide)) pre_rip
  have f467 : InstrSpec 0x104b15 [0x0F, 0xB7, 0x5C, 0x24, 0x6C] (LoadPre 0x104b15 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x104b15 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104b15 5 3 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104b15 5 3 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (movzx_r32_m16_effect_step 0x104b15 3 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f468 : InstrSpec 0x104b1a [0x89, 0xDD] (fun s => s.RIP = 0x104b1a) (movR32R32Effect 0x104b1a 2 5 3)
      [.gpr 3] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x104b1a 2 5 3).toInstrSpec (mov_r32_r32_effect_step 0x104b1a 0xdd (by decide)) pre_rip
  have f469 : InstrSpec 0x104b1c [0xC1, 0xED, 0x02] (fun s => s.RIP = 0x104b1c) (shrR32Effect 0x104b1c 3 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR32Effect_footprint 0x104b1c 3 5 2).toInstrSpec (shr_r32_imm8_effect_step 0x104b1c 0xed 0x2 (by decide) (by decide)) pre_rip
  have f470 : InstrSpec 0x104b1f [0x31, 0xDD] (fun s => s.RIP = 0x104b1f) (xorR32R32Effect 0x104b1f 2 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b1f 2 5 3).toInstrSpec (xor_r32_r32_effect_step 0x104b1f 0xdd (by decide)) pre_rip
  have f471 : InstrSpec 0x104b21 [0x81, 0xE5, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104b21) (andR32Imm32Effect 0x104b21 6 5 0x3030)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104b21 6 5 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x104b21 0xe5 0x3030 (by decide) (by decide)) pre_rip
  have f472 : InstrSpec 0x104b27 [0x31, 0xEB] (fun s => s.RIP = 0x104b27) (xorR32R32Effect 0x104b27 2 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b27 2 3 5).toInstrSpec (xor_r32_r32_effect_step 0x104b27 0xeb (by decide)) pre_rip
  have f473 : InstrSpec 0x104b29 [0xC1, 0xE5, 0x02] (fun s => s.RIP = 0x104b29) (shlR32Effect 0x104b29 3 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shlR32Effect_footprint 0x104b29 3 5 2).toInstrSpec (shl_r32_imm8_effect_step 0x104b29 0xe5 0x2 (by decide) (by decide)) pre_rip
  have f474 : InstrSpec 0x104b2c [0x31, 0xDD] (fun s => s.RIP = 0x104b2c) (xorR32R32Effect 0x104b2c 2 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b2c 2 5 3).toInstrSpec (xor_r32_r32_effect_step 0x104b2c 0xdd (by decide)) pre_rip
  have f475 : InstrSpec 0x104b2e [0x66, 0x89, 0x6C, 0x24, 0x6C] (StorePre 0x104b2e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x104b2e + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104b2e 5 5 (.sib 4 none 0 (.d8 0x6c)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104b2e 5 5 (.sib 4 none 0 (.d8 0x6c))).toInstrSpec (mov_m16_r16_effect_step 0x104b2e 5 (.sib 4 none 0 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f476 : InstrSpec 0x104b33 [0x0F, 0xB7, 0x5C, 0x24, 0x6E] (LoadPre 0x104b33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x104b33 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104b33 5 3 (.sib 4 none 0 (.d8 0x6e)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104b33 5 3 (.sib 4 none 0 (.d8 0x6e))).toInstrSpec (movzx_r32_m16_effect_step 0x104b33 3 (.sib 4 none 0 (.d8 0x6e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f477 : InstrSpec 0x104b38 [0x89, 0xDD] (fun s => s.RIP = 0x104b38) (movR32R32Effect 0x104b38 2 5 3)
      [.gpr 3] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x104b38 2 5 3).toInstrSpec (mov_r32_r32_effect_step 0x104b38 0xdd (by decide)) pre_rip
  have f478 : InstrSpec 0x104b3a [0xC1, 0xED, 0x02] (fun s => s.RIP = 0x104b3a) (shrR32Effect 0x104b3a 3 5 2)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR32Effect_footprint 0x104b3a 3 5 2).toInstrSpec (shr_r32_imm8_effect_step 0x104b3a 0xed 0x2 (by decide) (by decide)) pre_rip
  have f479 : InstrSpec 0x104b3d [0x31, 0xDD] (fun s => s.RIP = 0x104b3d) (xorR32R32Effect 0x104b3d 2 5 3)
      [.gpr 5, .gpr 3] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104b3d 2 5 3).toInstrSpec (xor_r32_r32_effect_step 0x104b3d 0xdd (by decide)) pre_rip
  refine Rest.ofInside (n := 946) (RestInside.out (n := 946) f460 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 947) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 944), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 946), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104afd) f460 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 948) (RestInside.out (n := 948) f461 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 949) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 944), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 948), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b01) f461 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 950) (RestInside.out (n := 950) f462 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 951) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 944), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 950), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b04) f462 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 952) (RestInside.out (n := 952) f463 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 953) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 944), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 952), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b0b) f463 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 954) (RestInside.out (n := 954) f464 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 955) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 954), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 952), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b0e) f464 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 956) (RestInside.out (n := 956) f465 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 957) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 954), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 956), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b12) f465 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 958) (RestInside.out (n := 958) f466 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 959) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 954), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b15) f466 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 960) (RestInside.out (n := 960) f467 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 961) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 960), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b1a) f467 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 962) (RestInside.out (n := 962) f468 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 963) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 960), (4, 4), (5, 962), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b1c) f468 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 964) (RestInside.out (n := 964) f469 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 965) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 960), (4, 4), (5, 964), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b1f) f469 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 966) (RestInside.out (n := 966) f470 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 967) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 960), (4, 4), (5, 966), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b21) f470 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 968) (RestInside.out (n := 968) f471 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 969) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 960), (4, 4), (5, 968), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b27) f471 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 970) (RestInside.out (n := 970) f472 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 971) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 970), (4, 4), (5, 968), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b29) f472 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 972) (RestInside.out (n := 972) f473 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 973) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 970), (4, 4), (5, 972), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b2c) f473 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 974) (RestInside.out (n := 974) f474 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 975) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 970), (4, 4), (5, 974), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b2e) f474 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 976) (RestInside.exec (n := 976) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 970), (4, 4), (5, 974), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b33) f475 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 977) (RestInside.out (n := 977) f476 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 978) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 977), (4, 4), (5, 974), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b38) f476 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 979) (RestInside.out (n := 979) f477 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 980) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 977), (4, 4), (5, 979), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b3a) f477 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 981) (RestInside.out (n := 981) f478 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 982) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 977), (4, 4), (5, 981), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b3d) f478 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 983) (RestInside.out (n := 983) f479 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 984) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 977), (4, 4), (5, 983), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 958), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104b3f) f479 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_24 code

theorem rest_l10446f_22 [Bindings] (code : CodeMap) :
    Rest (n := 907) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 897), (11, 905), (22, 22), (39, 39), (50, 50), (51, 51)]
      393 0x104aab bytes_l10446f_22 b_l10446f_22 := by
  have f440 : InstrSpec 0x104aab [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104aab) (xorR32R32Effect 0x104aab 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104aab 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104aab 0x45 0xda (by decide) (by decide)) pre_rip
  have f441 : InstrSpec 0x104aae [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x104aae) (shlR32Effect 0x104aae 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x104aae 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104aae 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f442 : InstrSpec 0x104ab2 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104ab2) (xorR32R32Effect 0x104ab2 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ab2 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ab2 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f443 : InstrSpec 0x104ab5 [0x45, 0x89, 0xDA] (fun s => s.RIP = 0x104ab5) (movR32R32Effect 0x104ab5 3 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x104ab5 3 10 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x104ab5 0x45 0xda (by decide) (by decide)) pre_rip
  have f444 : InstrSpec 0x104ab8 [0x41, 0xD1, 0xEA] (fun s => s.RIP = 0x104ab8) (shrR32Effect 0x104ab8 3 10 1)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x104ab8 3 10 1).toInstrSpec (shr_r32_one_rex_effect_step 0x104ab8 0x41 0xea (by decide) (by decide) (by decide)) pre_rip
  have f445 : InstrSpec 0x104abb [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104abb) (xorR32R32Effect 0x104abb 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104abb 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104abb 0x45 0xda (by decide) (by decide)) pre_rip
  have f446 : InstrSpec 0x104abe [0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104abe) (andR32Imm32Effect 0x104abe 7 10 0x5050)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104abe 7 10 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104abe 0x41 0xe2 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f447 : InstrSpec 0x104ac5 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104ac5) (xorR32R32Effect 0x104ac5 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ac5 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ac5 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f448 : InstrSpec 0x104ac8 [0x45, 0x01, 0xD2] (fun s => s.RIP = 0x104ac8) (addR32R32Effect 0x104ac8 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104ac8 3 10 10).toInstrSpec (add_r32_r32_rex_effect_step 0x104ac8 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f449 : InstrSpec 0x104acb [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104acb) (xorR32R32Effect 0x104acb 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104acb 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104acb 0x45 0xda (by decide) (by decide)) pre_rip
  have f450 : InstrSpec 0x104ace [0x66, 0x44, 0x89, 0x54, 0x24, 0x66] (StorePre 0x104ace 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x104ace + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104ace 6 10 (.sib 4 none 0 (.d8 0x66)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104ace 6 10 (.sib 4 none 0 (.d8 0x66))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104ace 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x66)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f451 : InstrSpec 0x104ad4 [0x44, 0x0F, 0xB7, 0x5C, 0x24, 0x68] (LoadPre 0x104ad4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x104ad4 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104ad4 6 11 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M16Effect_footprint 0x104ad4 6 11 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x104ad4 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f452 : InstrSpec 0x104ada [0x45, 0x89, 0xDA] (fun s => s.RIP = 0x104ada) (movR32R32Effect 0x104ada 3 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x104ada 3 10 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x104ada 0x45 0xda (by decide) (by decide)) pre_rip
  have f453 : InstrSpec 0x104add [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x104add) (shrR32Effect 0x104add 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x104add 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104add 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f454 : InstrSpec 0x104ae1 [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104ae1) (xorR32R32Effect 0x104ae1 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104ae1 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104ae1 0x45 0xda (by decide) (by decide)) pre_rip
  have f455 : InstrSpec 0x104ae4 [0x41, 0x81, 0xE2, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104ae4) (andR32Imm32Effect 0x104ae4 7 10 0x3030)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104ae4 7 10 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x104ae4 0x41 0xe2 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f456 : InstrSpec 0x104aeb [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104aeb) (xorR32R32Effect 0x104aeb 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104aeb 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104aeb 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f457 : InstrSpec 0x104aee [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x104aee) (shlR32Effect 0x104aee 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x104aee 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104aee 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f458 : InstrSpec 0x104af2 [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104af2) (xorR32R32Effect 0x104af2 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104af2 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104af2 0x45 0xda (by decide) (by decide)) pre_rip
  have f459 : InstrSpec 0x104af5 [0x0F, 0xB7, 0x5C, 0x24, 0x6A] (LoadPre 0x104af5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x104af5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104af5 5 3 (.sib 4 none 0 (.d8 0x6a)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movzxR32M16Effect_footprint 0x104af5 5 3 (.sib 4 none 0 (.d8 0x6a))).toInstrSpec (movzx_r32_m16_effect_step 0x104af5 3 (.sib 4 none 0 (.d8 0x6a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 907) (RestInside.out (n := 907) f440 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 908) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 907), (11, 905), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104aae) f440 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 909) (RestInside.out (n := 909) f441 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 910) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 907), (11, 909), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ab2) f441 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 911) (RestInside.out (n := 911) f442 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 912) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 907), (11, 911), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ab5) f442 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 913) (RestInside.out (n := 913) f443 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 914) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 913), (11, 911), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ab8) f443 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 915) (RestInside.out (n := 915) f444 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 916) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 915), (11, 911), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104abb) f444 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 917) (RestInside.out (n := 917) f445 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 918) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 917), (11, 911), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104abe) f445 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 919) (RestInside.out (n := 919) f446 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 920) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 919), (11, 911), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ac5) f446 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 921) (RestInside.out (n := 921) f447 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 922) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 919), (11, 921), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ac8) f447 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 923) (RestInside.out (n := 923) f448 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 924) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 923), (11, 921), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104acb) f448 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 925) (RestInside.out (n := 925) f449 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 926) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 925), (11, 921), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ace) f449 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 927) (RestInside.exec (n := 927) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 925), (11, 921), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ad4) f450 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 928) (RestInside.out (n := 928) f451 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 929) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 925), (11, 928), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ada) f451 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 930) (RestInside.out (n := 930) f452 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 931) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 930), (11, 928), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104add) f452 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 932) (RestInside.out (n := 932) f453 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 933) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 932), (11, 928), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ae1) f453 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 934) (RestInside.out (n := 934) f454 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 935) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 934), (11, 928), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104ae4) f454 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 936) (RestInside.out (n := 936) f455 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 937) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 936), (11, 928), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104aeb) f455 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 938) (RestInside.out (n := 938) f456 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 939) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 936), (11, 938), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104aee) f456 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 940) (RestInside.out (n := 940) f457 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 941) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 940), (11, 938), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104af2) f457 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 942) (RestInside.out (n := 942) f458 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 943) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 938), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104af5) f458 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 944) (RestInside.out (n := 944) f459 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 945) (ρ' := [(0, 315), (1, 332), (2, 311), (3, 944), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 942), (11, 938), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104afa) f459 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_23 code

theorem rest_l10446f_21 [Bindings] (code : CodeMap) :
    Rest (n := 868) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 866), (11, 859), (22, 22), (39, 39), (50, 50), (51, 51)]
      413 0x104a5a bytes_l10446f_21 b_l10446f_21 := by
  have f420 : InstrSpec 0x104a5a [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x104a5a) (movR32R32Effect 0x104a5a 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x104a5a 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x104a5a 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f421 : InstrSpec 0x104a5d [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x104a5d) (shrR32Effect 0x104a5d 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x104a5d 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104a5d 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f422 : InstrSpec 0x104a61 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104a61) (xorR32R32Effect 0x104a61 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a61 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a61 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f423 : InstrSpec 0x104a64 [0x41, 0x81, 0xE3, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104a64) (andR32Imm32Effect 0x104a64 7 11 0x1320)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104a64 7 11 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104a64 0x41 0xe3 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f424 : InstrSpec 0x104a6b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104a6b) (xorR32R32Effect 0x104a6b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a6b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a6b 0x45 0xda (by decide) (by decide)) pre_rip
  have f425 : InstrSpec 0x104a6e [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x104a6e) (shlR32Effect 0x104a6e 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x104a6e 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104a6e 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f426 : InstrSpec 0x104a72 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104a72) (xorR32R32Effect 0x104a72 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a72 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a72 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f427 : InstrSpec 0x104a75 [0x45, 0x89, 0xDA] (fun s => s.RIP = 0x104a75) (movR32R32Effect 0x104a75 3 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x104a75 3 10 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x104a75 0x45 0xda (by decide) (by decide)) pre_rip
  have f428 : InstrSpec 0x104a78 [0x41, 0xD1, 0xEA] (fun s => s.RIP = 0x104a78) (shrR32Effect 0x104a78 3 10 1)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x104a78 3 10 1).toInstrSpec (shr_r32_one_rex_effect_step 0x104a78 0x41 0xea (by decide) (by decide) (by decide)) pre_rip
  have f429 : InstrSpec 0x104a7b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104a7b) (xorR32R32Effect 0x104a7b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a7b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a7b 0x45 0xda (by decide) (by decide)) pre_rip
  have f430 : InstrSpec 0x104a7e [0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104a7e) (andR32Imm32Effect 0x104a7e 7 10 0x5050)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104a7e 7 10 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104a7e 0x41 0xe2 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f431 : InstrSpec 0x104a85 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104a85) (xorR32R32Effect 0x104a85 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a85 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a85 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f432 : InstrSpec 0x104a88 [0x45, 0x01, 0xD2] (fun s => s.RIP = 0x104a88) (addR32R32Effect 0x104a88 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104a88 3 10 10).toInstrSpec (add_r32_r32_rex_effect_step 0x104a88 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f433 : InstrSpec 0x104a8b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104a8b) (xorR32R32Effect 0x104a8b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a8b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a8b 0x45 0xda (by decide) (by decide)) pre_rip
  have f434 : InstrSpec 0x104a8e [0x66, 0x44, 0x89, 0x54, 0x24, 0x64] (StorePre 0x104a8e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x104a8e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104a8e 6 10 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104a8e 6 10 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104a8e 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f435 : InstrSpec 0x104a94 [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x66] (LoadPre 0x104a94 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x104a94 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104a94 6 10 (.sib 4 none 0 (.d8 0x66)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x104a94 6 10 (.sib 4 none 0 (.d8 0x66))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x104a94 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x66)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f436 : InstrSpec 0x104a9a [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x104a9a) (movR32R32Effect 0x104a9a 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x104a9a 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x104a9a 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f437 : InstrSpec 0x104a9d [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x104a9d) (shrR32Effect 0x104a9d 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x104a9d 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104a9d 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f438 : InstrSpec 0x104aa1 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104aa1) (xorR32R32Effect 0x104aa1 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104aa1 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104aa1 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f439 : InstrSpec 0x104aa4 [0x41, 0x81, 0xE3, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104aa4) (andR32Imm32Effect 0x104aa4 7 11 0x1320)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104aa4 7 11 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104aa4 0x41 0xe3 0x1320 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 868) (RestInside.out (n := 868) f420 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 869) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 866), (11, 868), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a5d) f420 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 870) (RestInside.out (n := 870) f421 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 871) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 866), (11, 870), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a61) f421 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 872) (RestInside.out (n := 872) f422 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 873) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 866), (11, 872), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a64) f422 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 874) (RestInside.out (n := 874) f423 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 875) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 866), (11, 874), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a6b) f423 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 876) (RestInside.out (n := 876) f424 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 877) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 876), (11, 874), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a6e) f424 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 878) (RestInside.out (n := 878) f425 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 879) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 876), (11, 878), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a72) f425 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 880) (RestInside.out (n := 880) f426 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 881) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 876), (11, 880), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a75) f426 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 882) (RestInside.out (n := 882) f427 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 883) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 882), (11, 880), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a78) f427 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 884) (RestInside.out (n := 884) f428 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 885) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 884), (11, 880), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a7b) f428 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 886) (RestInside.out (n := 886) f429 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 887) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 886), (11, 880), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a7e) f429 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 888) (RestInside.out (n := 888) f430 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 889) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 888), (11, 880), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a85) f430 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 890) (RestInside.out (n := 890) f431 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 891) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 888), (11, 890), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a88) f431 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 892) (RestInside.out (n := 892) f432 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 893) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 892), (11, 890), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a8b) f432 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 894) (RestInside.out (n := 894) f433 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 895) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 894), (11, 890), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a8e) f433 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 896) (RestInside.exec (n := 896) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 894), (11, 890), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a94) f434 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 897) (RestInside.out (n := 897) f435 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 898) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 897), (11, 890), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a9a) f435 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 899) (RestInside.out (n := 899) f436 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 900) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 897), (11, 899), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a9d) f436 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 901) (RestInside.out (n := 901) f437 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 902) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 897), (11, 901), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104aa1) f437 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 903) (RestInside.out (n := 903) f438 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 904) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 897), (11, 903), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104aa4) f438 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 905) (RestInside.out (n := 905) f439 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 906) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 897), (11, 905), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104aab) f439 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_22 code

theorem rest_l10446f_20 [Bindings] (code : CodeMap) :
    Rest (n := 830) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 826), (11, 828), (22, 22), (39, 39), (50, 50), (51, 51)]
      433 0x104a08 bytes_l10446f_20 b_l10446f_20 := by
  have f400 : InstrSpec 0x104a08 [0x45, 0x01, 0xD2] (fun s => s.RIP = 0x104a08) (addR32R32Effect 0x104a08 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104a08 3 10 10).toInstrSpec (add_r32_r32_rex_effect_step 0x104a08 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f401 : InstrSpec 0x104a0b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104a0b) (xorR32R32Effect 0x104a0b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a0b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a0b 0x45 0xda (by decide) (by decide)) pre_rip
  have f402 : InstrSpec 0x104a0e [0x66, 0x44, 0x89, 0x54, 0x24, 0x60] (StorePre 0x104a0e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x104a0e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104a0e 6 10 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104a0e 6 10 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104a0e 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f403 : InstrSpec 0x104a14 [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x62] (LoadPre 0x104a14 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x104a14 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104a14 6 10 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x104a14 6 10 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x104a14 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f404 : InstrSpec 0x104a1a [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x104a1a) (movR32R32Effect 0x104a1a 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x104a1a 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x104a1a 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f405 : InstrSpec 0x104a1d [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x104a1d) (shrR32Effect 0x104a1d 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x104a1d 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104a1d 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f406 : InstrSpec 0x104a21 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104a21) (xorR32R32Effect 0x104a21 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a21 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a21 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f407 : InstrSpec 0x104a24 [0x41, 0x81, 0xE3, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104a24) (andR32Imm32Effect 0x104a24 7 11 0x1320)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104a24 7 11 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104a24 0x41 0xe3 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f408 : InstrSpec 0x104a2b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104a2b) (xorR32R32Effect 0x104a2b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a2b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a2b 0x45 0xda (by decide) (by decide)) pre_rip
  have f409 : InstrSpec 0x104a2e [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x104a2e) (shlR32Effect 0x104a2e 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x104a2e 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104a2e 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f410 : InstrSpec 0x104a32 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104a32) (xorR32R32Effect 0x104a32 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a32 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a32 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f411 : InstrSpec 0x104a35 [0x45, 0x89, 0xDA] (fun s => s.RIP = 0x104a35) (movR32R32Effect 0x104a35 3 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x104a35 3 10 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x104a35 0x45 0xda (by decide) (by decide)) pre_rip
  have f412 : InstrSpec 0x104a38 [0x41, 0xD1, 0xEA] (fun s => s.RIP = 0x104a38) (shrR32Effect 0x104a38 3 10 1)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x104a38 3 10 1).toInstrSpec (shr_r32_one_rex_effect_step 0x104a38 0x41 0xea (by decide) (by decide) (by decide)) pre_rip
  have f413 : InstrSpec 0x104a3b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104a3b) (xorR32R32Effect 0x104a3b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a3b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a3b 0x45 0xda (by decide) (by decide)) pre_rip
  have f414 : InstrSpec 0x104a3e [0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104a3e) (andR32Imm32Effect 0x104a3e 7 10 0x5050)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104a3e 7 10 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104a3e 0x41 0xe2 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f415 : InstrSpec 0x104a45 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104a45) (xorR32R32Effect 0x104a45 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a45 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a45 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f416 : InstrSpec 0x104a48 [0x45, 0x01, 0xD2] (fun s => s.RIP = 0x104a48) (addR32R32Effect 0x104a48 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104a48 3 10 10).toInstrSpec (add_r32_r32_rex_effect_step 0x104a48 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f417 : InstrSpec 0x104a4b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x104a4b) (xorR32R32Effect 0x104a4b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a4b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a4b 0x45 0xda (by decide) (by decide)) pre_rip
  have f418 : InstrSpec 0x104a4e [0x66, 0x44, 0x89, 0x54, 0x24, 0x62] (StorePre 0x104a4e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x104a4e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104a4e 6 10 (.sib 4 none 0 (.d8 0x62)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104a4e 6 10 (.sib 4 none 0 (.d8 0x62))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104a4e 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x62)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f419 : InstrSpec 0x104a54 [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x64] (LoadPre 0x104a54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x104a54 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104a54 6 10 (.sib 4 none 0 (.d8 0x64)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x104a54 6 10 (.sib 4 none 0 (.d8 0x64))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x104a54 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x64)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 830) (RestInside.out (n := 830) f400 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 831) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 830), (11, 828), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a0b) f400 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 832) (RestInside.out (n := 832) f401 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 833) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 832), (11, 828), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a0e) f401 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 834) (RestInside.exec (n := 834) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 832), (11, 828), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a14) f402 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 835) (RestInside.out (n := 835) f403 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 836) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 835), (11, 828), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a1a) f403 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 837) (RestInside.out (n := 837) f404 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 838) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 835), (11, 837), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a1d) f404 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 839) (RestInside.out (n := 839) f405 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 840) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 835), (11, 839), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a21) f405 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 841) (RestInside.out (n := 841) f406 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 842) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 835), (11, 841), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a24) f406 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 843) (RestInside.out (n := 843) f407 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 844) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 835), (11, 843), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a2b) f407 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 845) (RestInside.out (n := 845) f408 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 846) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 845), (11, 843), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a2e) f408 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 847) (RestInside.out (n := 847) f409 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 848) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 845), (11, 847), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a32) f409 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 849) (RestInside.out (n := 849) f410 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 850) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 845), (11, 849), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a35) f410 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 851) (RestInside.out (n := 851) f411 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 852) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 851), (11, 849), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a38) f411 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 853) (RestInside.out (n := 853) f412 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 854) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 853), (11, 849), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a3b) f412 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 855) (RestInside.out (n := 855) f413 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 856) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 855), (11, 849), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a3e) f413 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 857) (RestInside.out (n := 857) f414 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 858) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 857), (11, 849), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a45) f414 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 859) (RestInside.out (n := 859) f415 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 860) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 857), (11, 859), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a48) f415 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 861) (RestInside.out (n := 861) f416 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 862) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 861), (11, 859), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a4b) f416 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 863) (RestInside.out (n := 863) f417 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 864) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 863), (11, 859), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a4e) f417 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 865) (RestInside.exec (n := 865) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 863), (11, 859), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a54) f418 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 866) (RestInside.out (n := 866) f419 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 867) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 866), (11, 859), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a5a) f419 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_21 code

theorem rest_l10446f_19 [Bindings] (code : CodeMap) :
    Rest (n := 791) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 789), (11, 787), (22, 22), (39, 39), (50, 50), (51, 51)]
      453 0x1049b8 bytes_l10446f_19 b_l10446f_19 := by
  have f380 : InstrSpec 0x1049b8 [0x41, 0xD1, 0xEA] (fun s => s.RIP = 0x1049b8) (shrR32Effect 0x1049b8 3 10 1)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x1049b8 3 10 1).toInstrSpec (shr_r32_one_rex_effect_step 0x1049b8 0x41 0xea (by decide) (by decide) (by decide)) pre_rip
  have f381 : InstrSpec 0x1049bb [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x1049bb) (xorR32R32Effect 0x1049bb 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1049bb 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1049bb 0x45 0xda (by decide) (by decide)) pre_rip
  have f382 : InstrSpec 0x1049be [0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1049be) (andR32Imm32Effect 0x1049be 7 10 0x5050)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1049be 7 10 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x1049be 0x41 0xe2 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f383 : InstrSpec 0x1049c5 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x1049c5) (xorR32R32Effect 0x1049c5 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1049c5 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1049c5 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f384 : InstrSpec 0x1049c8 [0x45, 0x01, 0xD2] (fun s => s.RIP = 0x1049c8) (addR32R32Effect 0x1049c8 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1049c8 3 10 10).toInstrSpec (add_r32_r32_rex_effect_step 0x1049c8 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f385 : InstrSpec 0x1049cb [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x1049cb) (xorR32R32Effect 0x1049cb 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1049cb 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1049cb 0x45 0xda (by decide) (by decide)) pre_rip
  have f386 : InstrSpec 0x1049ce [0x66, 0x44, 0x89, 0x54, 0x24, 0x5E] (StorePre 0x1049ce 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x1049ce + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1049ce 6 10 (.sib 4 none 0 (.d8 0x5e)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1049ce 6 10 (.sib 4 none 0 (.d8 0x5e))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1049ce 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x5e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f387 : InstrSpec 0x1049d4 [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x60] (LoadPre 0x1049d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1049d4 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1049d4 6 10 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x1049d4 6 10 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1049d4 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f388 : InstrSpec 0x1049da [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x1049da) (movR32R32Effect 0x1049da 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x1049da 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x1049da 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f389 : InstrSpec 0x1049dd [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x1049dd) (shrR32Effect 0x1049dd 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x1049dd 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1049dd 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f390 : InstrSpec 0x1049e1 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x1049e1) (xorR32R32Effect 0x1049e1 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1049e1 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1049e1 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f391 : InstrSpec 0x1049e4 [0x41, 0x81, 0xE3, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1049e4) (andR32Imm32Effect 0x1049e4 7 11 0x1320)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1049e4 7 11 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x1049e4 0x41 0xe3 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f392 : InstrSpec 0x1049eb [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x1049eb) (xorR32R32Effect 0x1049eb 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1049eb 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1049eb 0x45 0xda (by decide) (by decide)) pre_rip
  have f393 : InstrSpec 0x1049ee [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x1049ee) (shlR32Effect 0x1049ee 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x1049ee 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1049ee 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f394 : InstrSpec 0x1049f2 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x1049f2) (xorR32R32Effect 0x1049f2 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1049f2 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1049f2 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f395 : InstrSpec 0x1049f5 [0x45, 0x89, 0xDA] (fun s => s.RIP = 0x1049f5) (movR32R32Effect 0x1049f5 3 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1049f5 3 10 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x1049f5 0x45 0xda (by decide) (by decide)) pre_rip
  have f396 : InstrSpec 0x1049f8 [0x41, 0xD1, 0xEA] (fun s => s.RIP = 0x1049f8) (shrR32Effect 0x1049f8 3 10 1)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x1049f8 3 10 1).toInstrSpec (shr_r32_one_rex_effect_step 0x1049f8 0x41 0xea (by decide) (by decide) (by decide)) pre_rip
  have f397 : InstrSpec 0x1049fb [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x1049fb) (xorR32R32Effect 0x1049fb 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1049fb 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1049fb 0x45 0xda (by decide) (by decide)) pre_rip
  have f398 : InstrSpec 0x1049fe [0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1049fe) (andR32Imm32Effect 0x1049fe 7 10 0x5050)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1049fe 7 10 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x1049fe 0x41 0xe2 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f399 : InstrSpec 0x104a05 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104a05) (xorR32R32Effect 0x104a05 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104a05 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104a05 0x45 0xd3 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 791) (RestInside.out (n := 791) f380 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 792) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 791), (11, 787), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049bb) f380 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 793) (RestInside.out (n := 793) f381 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 794) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 793), (11, 787), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049be) f381 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 795) (RestInside.out (n := 795) f382 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 796) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 795), (11, 787), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049c5) f382 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 797) (RestInside.out (n := 797) f383 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 798) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 795), (11, 797), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049c8) f383 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 799) (RestInside.out (n := 799) f384 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 800) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 799), (11, 797), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049cb) f384 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 801) (RestInside.out (n := 801) f385 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 802) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 801), (11, 797), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049ce) f385 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 803) (RestInside.exec (n := 803) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 801), (11, 797), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049d4) f386 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 804) (RestInside.out (n := 804) f387 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 805) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 804), (11, 797), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049da) f387 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 806) (RestInside.out (n := 806) f388 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 807) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 804), (11, 806), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049dd) f388 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 808) (RestInside.out (n := 808) f389 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 809) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 804), (11, 808), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049e1) f389 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 810) (RestInside.out (n := 810) f390 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 811) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 804), (11, 810), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049e4) f390 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 812) (RestInside.out (n := 812) f391 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 813) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 804), (11, 812), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049eb) f391 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 814) (RestInside.out (n := 814) f392 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 815) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 814), (11, 812), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049ee) f392 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 816) (RestInside.out (n := 816) f393 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 817) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 814), (11, 816), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049f2) f393 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 818) (RestInside.out (n := 818) f394 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 819) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 814), (11, 818), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049f5) f394 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 820) (RestInside.out (n := 820) f395 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 821) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 820), (11, 818), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049f8) f395 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 822) (RestInside.out (n := 822) f396 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 823) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 822), (11, 818), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049fb) f396 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 824) (RestInside.out (n := 824) f397 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 825) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 824), (11, 818), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049fe) f397 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 826) (RestInside.out (n := 826) f398 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 827) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 826), (11, 818), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a05) f398 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 828) (RestInside.out (n := 828) f399 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 829) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 826), (11, 828), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104a08) f399 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_20 code

theorem rest_l10446f_18 [Bindings] (code : CodeMap) :
    Rest (n := 752) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 742), (11, 750), (22, 22), (39, 39), (50, 50), (51, 51)]
      473 0x10496b bytes_l10446f_18 b_l10446f_18 := by
  have f360 : InstrSpec 0x10496b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x10496b) (xorR32R32Effect 0x10496b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10496b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10496b 0x45 0xda (by decide) (by decide)) pre_rip
  have f361 : InstrSpec 0x10496e [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x10496e) (shlR32Effect 0x10496e 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x10496e 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10496e 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f362 : InstrSpec 0x104972 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104972) (xorR32R32Effect 0x104972 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104972 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104972 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f363 : InstrSpec 0x104975 [0x45, 0x89, 0xDA] (fun s => s.RIP = 0x104975) (movR32R32Effect 0x104975 3 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x104975 3 10 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x104975 0x45 0xda (by decide) (by decide)) pre_rip
  have f364 : InstrSpec 0x104978 [0x41, 0xD1, 0xEA] (fun s => s.RIP = 0x104978) (shrR32Effect 0x104978 3 10 1)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x104978 3 10 1).toInstrSpec (shr_r32_one_rex_effect_step 0x104978 0x41 0xea (by decide) (by decide) (by decide)) pre_rip
  have f365 : InstrSpec 0x10497b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x10497b) (xorR32R32Effect 0x10497b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10497b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10497b 0x45 0xda (by decide) (by decide)) pre_rip
  have f366 : InstrSpec 0x10497e [0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10497e) (andR32Imm32Effect 0x10497e 7 10 0x5050)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10497e 7 10 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x10497e 0x41 0xe2 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f367 : InstrSpec 0x104985 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104985) (xorR32R32Effect 0x104985 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104985 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104985 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f368 : InstrSpec 0x104988 [0x45, 0x01, 0xD2] (fun s => s.RIP = 0x104988) (addR32R32Effect 0x104988 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104988 3 10 10).toInstrSpec (add_r32_r32_rex_effect_step 0x104988 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f369 : InstrSpec 0x10498b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x10498b) (xorR32R32Effect 0x10498b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10498b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10498b 0x45 0xda (by decide) (by decide)) pre_rip
  have f370 : InstrSpec 0x10498e [0x66, 0x44, 0x89, 0x54, 0x24, 0x5C] (StorePre 0x10498e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x10498e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x10498e 6 10 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10498e 6 10 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (mov_m16_r16_rex_effect_step 0x10498e 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f371 : InstrSpec 0x104994 [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x5E] (LoadPre 0x104994 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x104994 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104994 6 10 (.sib 4 none 0 (.d8 0x5e)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x104994 6 10 (.sib 4 none 0 (.d8 0x5e))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x104994 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x5e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f372 : InstrSpec 0x10499a [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x10499a) (movR32R32Effect 0x10499a 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x10499a 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x10499a 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f373 : InstrSpec 0x10499d [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x10499d) (shrR32Effect 0x10499d 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x10499d 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10499d 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f374 : InstrSpec 0x1049a1 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x1049a1) (xorR32R32Effect 0x1049a1 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1049a1 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1049a1 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f375 : InstrSpec 0x1049a4 [0x41, 0x81, 0xE3, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1049a4) (andR32Imm32Effect 0x1049a4 7 11 0x1320)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1049a4 7 11 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x1049a4 0x41 0xe3 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f376 : InstrSpec 0x1049ab [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x1049ab) (xorR32R32Effect 0x1049ab 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1049ab 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x1049ab 0x45 0xda (by decide) (by decide)) pre_rip
  have f377 : InstrSpec 0x1049ae [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x1049ae) (shlR32Effect 0x1049ae 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x1049ae 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1049ae 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f378 : InstrSpec 0x1049b2 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x1049b2) (xorR32R32Effect 0x1049b2 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1049b2 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1049b2 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f379 : InstrSpec 0x1049b5 [0x45, 0x89, 0xDA] (fun s => s.RIP = 0x1049b5) (movR32R32Effect 0x1049b5 3 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1049b5 3 10 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x1049b5 0x45 0xda (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 752) (RestInside.out (n := 752) f360 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 753) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 752), (11, 750), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10496e) f360 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 754) (RestInside.out (n := 754) f361 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 755) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 752), (11, 754), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104972) f361 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 756) (RestInside.out (n := 756) f362 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 757) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 752), (11, 756), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104975) f362 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 758) (RestInside.out (n := 758) f363 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 759) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 758), (11, 756), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104978) f363 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 760) (RestInside.out (n := 760) f364 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 761) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 760), (11, 756), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10497b) f364 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 762) (RestInside.out (n := 762) f365 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 763) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 762), (11, 756), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10497e) f365 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 764) (RestInside.out (n := 764) f366 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 765) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 764), (11, 756), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104985) f366 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 766) (RestInside.out (n := 766) f367 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 767) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 764), (11, 766), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104988) f367 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 768) (RestInside.out (n := 768) f368 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 769) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 768), (11, 766), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10498b) f368 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 770) (RestInside.out (n := 770) f369 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 771) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 770), (11, 766), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10498e) f369 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 772) (RestInside.exec (n := 772) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 770), (11, 766), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104994) f370 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 773) (RestInside.out (n := 773) f371 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 774) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 773), (11, 766), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10499a) f371 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 775) (RestInside.out (n := 775) f372 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 776) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 773), (11, 775), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10499d) f372 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 777) (RestInside.out (n := 777) f373 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 778) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 773), (11, 777), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049a1) f373 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 779) (RestInside.out (n := 779) f374 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 780) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 773), (11, 779), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049a4) f374 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 781) (RestInside.out (n := 781) f375 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 782) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 773), (11, 781), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049ab) f375 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 783) (RestInside.out (n := 783) f376 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 784) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 783), (11, 781), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049ae) f376 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 785) (RestInside.out (n := 785) f377 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 786) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 783), (11, 785), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049b2) f377 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 787) (RestInside.out (n := 787) f378 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 788) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 783), (11, 787), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049b5) f378 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 789) (RestInside.out (n := 789) f379 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 790) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 789), (11, 787), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1049b8) f379 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_19 code

theorem rest_l10446f_17 [Bindings] (code : CodeMap) :
    Rest (n := 713) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 711), (22, 22), (39, 39), (50, 50), (51, 51)]
      493 0x10491a bytes_l10446f_17 b_l10446f_17 := by
  have f340 : InstrSpec 0x10491a [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x10491a) (movR32R32Effect 0x10491a 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x10491a 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x10491a 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f341 : InstrSpec 0x10491d [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x10491d) (shrR32Effect 0x10491d 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x10491d 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10491d 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f342 : InstrSpec 0x104921 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104921) (xorR32R32Effect 0x104921 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104921 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104921 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f343 : InstrSpec 0x104924 [0x41, 0x81, 0xE3, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104924) (andR32Imm32Effect 0x104924 7 11 0x1320)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104924 7 11 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104924 0x41 0xe3 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f344 : InstrSpec 0x10492b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x10492b) (xorR32R32Effect 0x10492b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10492b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10492b 0x45 0xda (by decide) (by decide)) pre_rip
  have f345 : InstrSpec 0x10492e [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x10492e) (shlR32Effect 0x10492e 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x10492e 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10492e 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f346 : InstrSpec 0x104932 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104932) (xorR32R32Effect 0x104932 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104932 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104932 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f347 : InstrSpec 0x104935 [0x45, 0x89, 0xDA] (fun s => s.RIP = 0x104935) (movR32R32Effect 0x104935 3 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x104935 3 10 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x104935 0x45 0xda (by decide) (by decide)) pre_rip
  have f348 : InstrSpec 0x104938 [0x41, 0xD1, 0xEA] (fun s => s.RIP = 0x104938) (shrR32Effect 0x104938 3 10 1)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x104938 3 10 1).toInstrSpec (shr_r32_one_rex_effect_step 0x104938 0x41 0xea (by decide) (by decide) (by decide)) pre_rip
  have f349 : InstrSpec 0x10493b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x10493b) (xorR32R32Effect 0x10493b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10493b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10493b 0x45 0xda (by decide) (by decide)) pre_rip
  have f350 : InstrSpec 0x10493e [0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10493e) (andR32Imm32Effect 0x10493e 7 10 0x5050)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10493e 7 10 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x10493e 0x41 0xe2 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f351 : InstrSpec 0x104945 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104945) (xorR32R32Effect 0x104945 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104945 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104945 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f352 : InstrSpec 0x104948 [0x45, 0x01, 0xD2] (fun s => s.RIP = 0x104948) (addR32R32Effect 0x104948 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104948 3 10 10).toInstrSpec (add_r32_r32_rex_effect_step 0x104948 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f353 : InstrSpec 0x10494b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x10494b) (xorR32R32Effect 0x10494b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10494b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10494b 0x45 0xda (by decide) (by decide)) pre_rip
  have f354 : InstrSpec 0x10494e [0x66, 0x44, 0x89, 0x54, 0x24, 0x5A] (StorePre 0x10494e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x10494e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x10494e 6 10 (.sib 4 none 0 (.d8 0x5a)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10494e 6 10 (.sib 4 none 0 (.d8 0x5a))).toInstrSpec (mov_m16_r16_rex_effect_step 0x10494e 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x5a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f355 : InstrSpec 0x104954 [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x5C] (LoadPre 0x104954 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x104954 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104954 6 10 (.sib 4 none 0 (.d8 0x5c)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x104954 6 10 (.sib 4 none 0 (.d8 0x5c))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x104954 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x5c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f356 : InstrSpec 0x10495a [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x10495a) (movR32R32Effect 0x10495a 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x10495a 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x10495a 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f357 : InstrSpec 0x10495d [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x10495d) (shrR32Effect 0x10495d 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x10495d 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10495d 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f358 : InstrSpec 0x104961 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x104961) (xorR32R32Effect 0x104961 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104961 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104961 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f359 : InstrSpec 0x104964 [0x41, 0x81, 0xE3, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x104964) (andR32Imm32Effect 0x104964 7 11 0x1320)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104964 7 11 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x104964 0x41 0xe3 0x1320 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 713) (RestInside.out (n := 713) f340 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 714) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 711), (11, 713), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10491d) f340 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 715) (RestInside.out (n := 715) f341 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 716) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 711), (11, 715), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104921) f341 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 717) (RestInside.out (n := 717) f342 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 718) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 711), (11, 717), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104924) f342 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 719) (RestInside.out (n := 719) f343 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 720) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 711), (11, 719), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10492b) f343 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 721) (RestInside.out (n := 721) f344 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 722) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 721), (11, 719), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10492e) f344 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 723) (RestInside.out (n := 723) f345 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 724) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 721), (11, 723), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104932) f345 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 725) (RestInside.out (n := 725) f346 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 726) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 721), (11, 725), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104935) f346 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 727) (RestInside.out (n := 727) f347 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 728) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 727), (11, 725), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104938) f347 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 729) (RestInside.out (n := 729) f348 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 730) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 729), (11, 725), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10493b) f348 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 731) (RestInside.out (n := 731) f349 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 732) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 731), (11, 725), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10493e) f349 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 733) (RestInside.out (n := 733) f350 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 734) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 733), (11, 725), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104945) f350 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 735) (RestInside.out (n := 735) f351 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 736) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 733), (11, 735), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104948) f351 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 737) (RestInside.out (n := 737) f352 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 738) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 737), (11, 735), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10494b) f352 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 739) (RestInside.out (n := 739) f353 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 740) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 739), (11, 735), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10494e) f353 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 741) (RestInside.exec (n := 741) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 739), (11, 735), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104954) f354 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 742) (RestInside.out (n := 742) f355 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 743) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 742), (11, 735), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10495a) f355 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 744) (RestInside.out (n := 744) f356 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 745) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 742), (11, 744), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10495d) f356 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 746) (RestInside.out (n := 746) f357 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 747) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 742), (11, 746), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104961) f357 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 748) (RestInside.out (n := 748) f358 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 749) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 742), (11, 748), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104964) f358 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 750) (RestInside.out (n := 750) f359 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 751) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 742), (11, 750), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10496b) f359 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_18 code

theorem rest_l10446f_16 [Bindings] (code : CodeMap) :
    Rest (n := 674) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 672), (10, 664), (22, 22), (39, 39), (50, 50), (51, 51)]
      513 0x1048cb bytes_l10446f_16 b_l10446f_16 := by
  have f320 : InstrSpec 0x1048cb [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x1048cb) (xorR32R32Effect 0x1048cb 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1048cb 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1048cb 0x45 0xca (by decide) (by decide)) pre_rip
  have f321 : InstrSpec 0x1048ce [0x45, 0x01, 0xC9] (fun s => s.RIP = 0x1048ce) (addR32R32Effect 0x1048ce 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1048ce 3 9 9).toInstrSpec (add_r32_r32_rex_effect_step 0x1048ce 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f322 : InstrSpec 0x1048d1 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x1048d1) (xorR32R32Effect 0x1048d1 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1048d1 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1048d1 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f323 : InstrSpec 0x1048d4 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x46] (StorePre 0x1048d4 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x1048d4 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1048d4 6 9 (.sib 4 none 0 (.d8 0x46)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1048d4 6 9 (.sib 4 none 0 (.d8 0x46))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1048d4 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x46)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f324 : InstrSpec 0x1048da [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x58] (LoadPre 0x1048da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1048da + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1048da 6 9 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x1048da 6 9 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1048da 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f325 : InstrSpec 0x1048e0 [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x1048e0) (movR32R32Effect 0x1048e0 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1048e0 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x1048e0 0x45 0xca (by decide) (by decide)) pre_rip
  have f326 : InstrSpec 0x1048e3 [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x1048e3) (shrR32Effect 0x1048e3 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x1048e3 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1048e3 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f327 : InstrSpec 0x1048e7 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x1048e7) (xorR32R32Effect 0x1048e7 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1048e7 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1048e7 0x45 0xca (by decide) (by decide)) pre_rip
  have f328 : InstrSpec 0x1048ea [0x41, 0x81, 0xE2, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1048ea) (andR32Imm32Effect 0x1048ea 7 10 0x1320)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1048ea 7 10 0x1320).toInstrSpec (and_r32_imm32_rex_effect_step 0x1048ea 0x41 0xe2 0x1320 (by decide) (by decide) (by decide)) pre_rip
  have f329 : InstrSpec 0x1048f1 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x1048f1) (xorR32R32Effect 0x1048f1 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1048f1 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1048f1 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f330 : InstrSpec 0x1048f4 [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x1048f4) (shlR32Effect 0x1048f4 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x1048f4 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1048f4 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f331 : InstrSpec 0x1048f8 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x1048f8) (xorR32R32Effect 0x1048f8 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1048f8 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1048f8 0x45 0xca (by decide) (by decide)) pre_rip
  have f332 : InstrSpec 0x1048fb [0x45, 0x89, 0xD1] (fun s => s.RIP = 0x1048fb) (movR32R32Effect 0x1048fb 3 9 10)
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1048fb 3 9 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x1048fb 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f333 : InstrSpec 0x1048fe [0x41, 0xD1, 0xE9] (fun s => s.RIP = 0x1048fe) (shrR32Effect 0x1048fe 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x1048fe 3 9 1).toInstrSpec (shr_r32_one_rex_effect_step 0x1048fe 0x41 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f334 : InstrSpec 0x104901 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104901) (xorR32R32Effect 0x104901 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104901 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104901 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f335 : InstrSpec 0x104904 [0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104904) (andR32Imm32Effect 0x104904 7 9 0x5050)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104904 7 9 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104904 0x41 0xe1 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f336 : InstrSpec 0x10490b [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x10490b) (xorR32R32Effect 0x10490b 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10490b 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10490b 0x45 0xca (by decide) (by decide)) pre_rip
  have f337 : InstrSpec 0x10490e [0x45, 0x01, 0xC9] (fun s => s.RIP = 0x10490e) (addR32R32Effect 0x10490e 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10490e 3 9 9).toInstrSpec (add_r32_r32_rex_effect_step 0x10490e 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f338 : InstrSpec 0x104911 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104911) (xorR32R32Effect 0x104911 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104911 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104911 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f339 : InstrSpec 0x104914 [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x5A] (LoadPre 0x104914 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5a)) s (0x104914 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104914 6 10 (.sib 4 none 0 (.d8 0x5a)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x104914 6 10 (.sib 4 none 0 (.d8 0x5a))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x104914 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x5a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 674) (RestInside.out (n := 674) f320 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 675) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 672), (10, 674), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048ce) f320 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 676) (RestInside.out (n := 676) f321 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 677) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 676), (10, 674), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048d1) f321 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 678) (RestInside.out (n := 678) f322 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 679) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 678), (10, 674), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048d4) f322 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 680) (RestInside.exec (n := 680) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 678), (10, 674), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048da) f323 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 681) (RestInside.out (n := 681) f324 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 682) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 681), (10, 674), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048e0) f324 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 683) (RestInside.out (n := 683) f325 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 684) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 681), (10, 683), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048e3) f325 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 685) (RestInside.out (n := 685) f326 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 686) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 681), (10, 685), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048e7) f326 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 687) (RestInside.out (n := 687) f327 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 688) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 681), (10, 687), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048ea) f327 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 689) (RestInside.out (n := 689) f328 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 690) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 681), (10, 689), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048f1) f328 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 691) (RestInside.out (n := 691) f329 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 692) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 691), (10, 689), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048f4) f329 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 693) (RestInside.out (n := 693) f330 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 694) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 691), (10, 693), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048f8) f330 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 695) (RestInside.out (n := 695) f331 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 696) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 691), (10, 695), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048fb) f331 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 697) (RestInside.out (n := 697) f332 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 698) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 697), (10, 695), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048fe) f332 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 699) (RestInside.out (n := 699) f333 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 700) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 699), (10, 695), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104901) f333 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 701) (RestInside.out (n := 701) f334 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 702) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 701), (10, 695), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104904) f334 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 703) (RestInside.out (n := 703) f335 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 704) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 703), (10, 695), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10490b) f335 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 705) (RestInside.out (n := 705) f336 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 706) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 703), (10, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10490e) f336 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 707) (RestInside.out (n := 707) f337 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 708) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 707), (10, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104911) f337 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 709) (RestInside.out (n := 709) f338 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 710) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 705), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104914) f338 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 711) (RestInside.out (n := 711) f339 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 712) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 709), (10, 711), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10491a) f339 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_17 code

theorem rest_l10446f_15 [Bindings] (code : CodeMap) :
    Rest (n := 635) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 629), (10, 633), (22, 22), (39, 39), (50, 50), (51, 51)]
      533 0x10487b bytes_l10446f_15 b_l10446f_15 := by
  have f300 : InstrSpec 0x10487b [0x45, 0x89, 0xD1] (fun s => s.RIP = 0x10487b) (movR32R32Effect 0x10487b 3 9 10)
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x10487b 3 9 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x10487b 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f301 : InstrSpec 0x10487e [0x41, 0xD1, 0xE9] (fun s => s.RIP = 0x10487e) (shrR32Effect 0x10487e 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x10487e 3 9 1).toInstrSpec (shr_r32_one_rex_effect_step 0x10487e 0x41 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f302 : InstrSpec 0x104881 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104881) (xorR32R32Effect 0x104881 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104881 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104881 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f303 : InstrSpec 0x104884 [0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104884) (andR32Imm32Effect 0x104884 7 9 0x5050)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104884 7 9 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104884 0x41 0xe1 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f304 : InstrSpec 0x10488b [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x10488b) (xorR32R32Effect 0x10488b 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10488b 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10488b 0x45 0xca (by decide) (by decide)) pre_rip
  have f305 : InstrSpec 0x10488e [0x45, 0x01, 0xC9] (fun s => s.RIP = 0x10488e) (addR32R32Effect 0x10488e 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10488e 3 9 9).toInstrSpec (add_r32_r32_rex_effect_step 0x10488e 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f306 : InstrSpec 0x104891 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104891) (xorR32R32Effect 0x104891 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104891 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104891 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f307 : InstrSpec 0x104894 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x44] (StorePre 0x104894 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x104894 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104894 6 9 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104894 6 9 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104894 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f308 : InstrSpec 0x10489a [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x46] (LoadPre 0x10489a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x10489a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10489a 6 9 (.sib 4 none 0 (.d8 0x46)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x10489a 6 9 (.sib 4 none 0 (.d8 0x46))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10489a 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x46)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f309 : InstrSpec 0x1048a0 [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x1048a0) (movR32R32Effect 0x1048a0 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1048a0 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x1048a0 0x45 0xca (by decide) (by decide)) pre_rip
  have f310 : InstrSpec 0x1048a3 [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x1048a3) (shrR32Effect 0x1048a3 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x1048a3 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1048a3 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f311 : InstrSpec 0x1048a7 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x1048a7) (xorR32R32Effect 0x1048a7 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1048a7 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1048a7 0x45 0xca (by decide) (by decide)) pre_rip
  have f312 : InstrSpec 0x1048aa [0x41, 0x81, 0xE2, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x1048aa) (andR32Imm32Effect 0x1048aa 7 10 0x2310)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1048aa 7 10 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x1048aa 0x41 0xe2 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f313 : InstrSpec 0x1048b1 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x1048b1) (xorR32R32Effect 0x1048b1 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1048b1 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1048b1 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f314 : InstrSpec 0x1048b4 [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x1048b4) (shlR32Effect 0x1048b4 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x1048b4 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1048b4 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f315 : InstrSpec 0x1048b8 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x1048b8) (xorR32R32Effect 0x1048b8 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1048b8 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1048b8 0x45 0xca (by decide) (by decide)) pre_rip
  have f316 : InstrSpec 0x1048bb [0x45, 0x89, 0xD1] (fun s => s.RIP = 0x1048bb) (movR32R32Effect 0x1048bb 3 9 10)
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1048bb 3 9 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x1048bb 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f317 : InstrSpec 0x1048be [0x41, 0xD1, 0xE9] (fun s => s.RIP = 0x1048be) (shrR32Effect 0x1048be 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x1048be 3 9 1).toInstrSpec (shr_r32_one_rex_effect_step 0x1048be 0x41 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f318 : InstrSpec 0x1048c1 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x1048c1) (xorR32R32Effect 0x1048c1 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1048c1 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1048c1 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f319 : InstrSpec 0x1048c4 [0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1048c4) (andR32Imm32Effect 0x1048c4 7 9 0x5050)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1048c4 7 9 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x1048c4 0x41 0xe1 0x5050 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 635) (RestInside.out (n := 635) f300 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 636) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 635), (10, 633), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10487e) f300 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 637) (RestInside.out (n := 637) f301 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 638) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 637), (10, 633), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104881) f301 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 639) (RestInside.out (n := 639) f302 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 640) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 639), (10, 633), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104884) f302 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 641) (RestInside.out (n := 641) f303 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 642) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 641), (10, 633), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10488b) f303 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 643) (RestInside.out (n := 643) f304 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 644) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 641), (10, 643), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10488e) f304 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 645) (RestInside.out (n := 645) f305 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 646) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 645), (10, 643), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104891) f305 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 647) (RestInside.out (n := 647) f306 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 648) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 647), (10, 643), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104894) f306 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 649) (RestInside.exec (n := 649) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 647), (10, 643), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10489a) f307 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 650) (RestInside.out (n := 650) f308 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 651) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 650), (10, 643), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048a0) f308 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 652) (RestInside.out (n := 652) f309 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 653) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 650), (10, 652), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048a3) f309 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 654) (RestInside.out (n := 654) f310 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 655) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 650), (10, 654), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048a7) f310 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 656) (RestInside.out (n := 656) f311 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 657) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 650), (10, 656), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048aa) f311 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 658) (RestInside.out (n := 658) f312 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 659) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 650), (10, 658), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048b1) f312 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 660) (RestInside.out (n := 660) f313 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 661) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 660), (10, 658), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048b4) f313 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 662) (RestInside.out (n := 662) f314 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 663) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 660), (10, 662), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048b8) f314 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 664) (RestInside.out (n := 664) f315 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 665) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 660), (10, 664), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048bb) f315 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 666) (RestInside.out (n := 666) f316 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 667) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 666), (10, 664), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048be) f316 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 668) (RestInside.out (n := 668) f317 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 669) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 668), (10, 664), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048c1) f317 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 670) (RestInside.out (n := 670) f318 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 671) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 670), (10, 664), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048c4) f318 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 672) (RestInside.out (n := 672) f319 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 673) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 672), (10, 664), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1048cb) f319 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_16 code

theorem rest_l10446f_14 [Bindings] (code : CodeMap) :
    Rest (n := 596) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 588), (10, 594), (22, 22), (39, 39), (50, 50), (51, 51)]
      553 0x10482a bytes_l10446f_14 b_l10446f_14 := by
  have f280 : InstrSpec 0x10482a [0x41, 0x81, 0xE2, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x10482a) (andR32Imm32Effect 0x10482a 7 10 0x2310)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10482a 7 10 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x10482a 0x41 0xe2 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f281 : InstrSpec 0x104831 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104831) (xorR32R32Effect 0x104831 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104831 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104831 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f282 : InstrSpec 0x104834 [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x104834) (shlR32Effect 0x104834 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x104834 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104834 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f283 : InstrSpec 0x104838 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x104838) (xorR32R32Effect 0x104838 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104838 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104838 0x45 0xca (by decide) (by decide)) pre_rip
  have f284 : InstrSpec 0x10483b [0x45, 0x89, 0xD1] (fun s => s.RIP = 0x10483b) (movR32R32Effect 0x10483b 3 9 10)
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x10483b 3 9 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x10483b 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f285 : InstrSpec 0x10483e [0x41, 0xD1, 0xE9] (fun s => s.RIP = 0x10483e) (shrR32Effect 0x10483e 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x10483e 3 9 1).toInstrSpec (shr_r32_one_rex_effect_step 0x10483e 0x41 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f286 : InstrSpec 0x104841 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104841) (xorR32R32Effect 0x104841 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104841 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104841 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f287 : InstrSpec 0x104844 [0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104844) (andR32Imm32Effect 0x104844 7 9 0x5050)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104844 7 9 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104844 0x41 0xe1 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f288 : InstrSpec 0x10484b [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x10484b) (xorR32R32Effect 0x10484b 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10484b 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10484b 0x45 0xca (by decide) (by decide)) pre_rip
  have f289 : InstrSpec 0x10484e [0x45, 0x01, 0xC9] (fun s => s.RIP = 0x10484e) (addR32R32Effect 0x10484e 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10484e 3 9 9).toInstrSpec (add_r32_r32_rex_effect_step 0x10484e 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f290 : InstrSpec 0x104851 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104851) (xorR32R32Effect 0x104851 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104851 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104851 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f291 : InstrSpec 0x104854 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x42] (StorePre 0x104854 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x104854 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104854 6 9 (.sib 4 none 0 (.d8 0x42)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104854 6 9 (.sib 4 none 0 (.d8 0x42))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104854 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f292 : InstrSpec 0x10485a [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x44] (LoadPre 0x10485a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x10485a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10485a 6 9 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x10485a 6 9 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10485a 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f293 : InstrSpec 0x104860 [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x104860) (movR32R32Effect 0x104860 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x104860 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x104860 0x45 0xca (by decide) (by decide)) pre_rip
  have f294 : InstrSpec 0x104863 [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x104863) (shrR32Effect 0x104863 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x104863 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104863 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f295 : InstrSpec 0x104867 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x104867) (xorR32R32Effect 0x104867 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104867 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104867 0x45 0xca (by decide) (by decide)) pre_rip
  have f296 : InstrSpec 0x10486a [0x41, 0x81, 0xE2, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x10486a) (andR32Imm32Effect 0x10486a 7 10 0x2310)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10486a 7 10 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x10486a 0x41 0xe2 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f297 : InstrSpec 0x104871 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104871) (xorR32R32Effect 0x104871 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104871 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104871 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f298 : InstrSpec 0x104874 [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x104874) (shlR32Effect 0x104874 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x104874 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104874 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f299 : InstrSpec 0x104878 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x104878) (xorR32R32Effect 0x104878 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104878 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104878 0x45 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 596) (RestInside.out (n := 596) f280 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 597) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 588), (10, 596), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104831) f280 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 598) (RestInside.out (n := 598) f281 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 599) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 598), (10, 596), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104834) f281 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 600) (RestInside.out (n := 600) f282 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 601) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 598), (10, 600), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104838) f282 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 602) (RestInside.out (n := 602) f283 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 603) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 598), (10, 602), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10483b) f283 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 604) (RestInside.out (n := 604) f284 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 605) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 604), (10, 602), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10483e) f284 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 606) (RestInside.out (n := 606) f285 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 607) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 606), (10, 602), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104841) f285 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 608) (RestInside.out (n := 608) f286 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 609) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 608), (10, 602), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104844) f286 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 610) (RestInside.out (n := 610) f287 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 611) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 610), (10, 602), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10484b) f287 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 612) (RestInside.out (n := 612) f288 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 613) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 610), (10, 612), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10484e) f288 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 614) (RestInside.out (n := 614) f289 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 615) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 614), (10, 612), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104851) f289 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 616) (RestInside.out (n := 616) f290 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 617) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 616), (10, 612), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104854) f290 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 618) (RestInside.exec (n := 618) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 616), (10, 612), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10485a) f291 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 619) (RestInside.out (n := 619) f292 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 620) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 619), (10, 612), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104860) f292 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 621) (RestInside.out (n := 621) f293 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 622) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 619), (10, 621), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104863) f293 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 623) (RestInside.out (n := 623) f294 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 624) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 619), (10, 623), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104867) f294 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 625) (RestInside.out (n := 625) f295 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 626) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 619), (10, 625), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10486a) f295 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 627) (RestInside.out (n := 627) f296 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 628) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 619), (10, 627), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104871) f296 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 629) (RestInside.out (n := 629) f297 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 630) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 629), (10, 627), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104874) f297 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 631) (RestInside.out (n := 631) f298 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 632) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 629), (10, 631), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104878) f298 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 633) (RestInside.out (n := 633) f299 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 634) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 629), (10, 633), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10487b) f299 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_15 code

theorem rest_l10446f_13 [Bindings] (code : CodeMap) :
    Rest (n := 557) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 554), (10, 550), (22, 22), (39, 39), (50, 50), (51, 51)]
      573 0x1047da bytes_l10446f_13 b_l10446f_13 := by
  have f260 : InstrSpec 0x1047da [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x40] (LoadPre 0x1047da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1047da + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1047da 6 9 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x1047da 6 9 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1047da 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f261 : InstrSpec 0x1047e0 [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x1047e0) (movR32R32Effect 0x1047e0 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1047e0 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x1047e0 0x45 0xca (by decide) (by decide)) pre_rip
  have f262 : InstrSpec 0x1047e3 [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x1047e3) (shrR32Effect 0x1047e3 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x1047e3 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1047e3 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f263 : InstrSpec 0x1047e7 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x1047e7) (xorR32R32Effect 0x1047e7 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1047e7 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1047e7 0x45 0xca (by decide) (by decide)) pre_rip
  have f264 : InstrSpec 0x1047ea [0x41, 0x81, 0xE2, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x1047ea) (andR32Imm32Effect 0x1047ea 7 10 0x2310)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1047ea 7 10 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x1047ea 0x41 0xe2 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f265 : InstrSpec 0x1047f1 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x1047f1) (xorR32R32Effect 0x1047f1 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1047f1 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1047f1 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f266 : InstrSpec 0x1047f4 [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x1047f4) (shlR32Effect 0x1047f4 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x1047f4 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1047f4 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f267 : InstrSpec 0x1047f8 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x1047f8) (xorR32R32Effect 0x1047f8 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1047f8 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1047f8 0x45 0xca (by decide) (by decide)) pre_rip
  have f268 : InstrSpec 0x1047fb [0x45, 0x89, 0xD1] (fun s => s.RIP = 0x1047fb) (movR32R32Effect 0x1047fb 3 9 10)
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1047fb 3 9 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x1047fb 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f269 : InstrSpec 0x1047fe [0x41, 0xD1, 0xE9] (fun s => s.RIP = 0x1047fe) (shrR32Effect 0x1047fe 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x1047fe 3 9 1).toInstrSpec (shr_r32_one_rex_effect_step 0x1047fe 0x41 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f270 : InstrSpec 0x104801 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104801) (xorR32R32Effect 0x104801 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104801 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104801 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f271 : InstrSpec 0x104804 [0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104804) (andR32Imm32Effect 0x104804 7 9 0x5050)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104804 7 9 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104804 0x41 0xe1 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f272 : InstrSpec 0x10480b [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x10480b) (xorR32R32Effect 0x10480b 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10480b 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10480b 0x45 0xca (by decide) (by decide)) pre_rip
  have f273 : InstrSpec 0x10480e [0x45, 0x01, 0xC9] (fun s => s.RIP = 0x10480e) (addR32R32Effect 0x10480e 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10480e 3 9 9).toInstrSpec (add_r32_r32_rex_effect_step 0x10480e 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f274 : InstrSpec 0x104811 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104811) (xorR32R32Effect 0x104811 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104811 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104811 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f275 : InstrSpec 0x104814 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x40] (StorePre 0x104814 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x104814 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104814 6 9 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104814 6 9 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104814 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f276 : InstrSpec 0x10481a [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x42] (LoadPre 0x10481a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x10481a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10481a 6 9 (.sib 4 none 0 (.d8 0x42)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x10481a 6 9 (.sib 4 none 0 (.d8 0x42))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10481a 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f277 : InstrSpec 0x104820 [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x104820) (movR32R32Effect 0x104820 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x104820 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x104820 0x45 0xca (by decide) (by decide)) pre_rip
  have f278 : InstrSpec 0x104823 [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x104823) (shrR32Effect 0x104823 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x104823 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104823 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f279 : InstrSpec 0x104827 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x104827) (xorR32R32Effect 0x104827 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104827 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104827 0x45 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 557) (RestInside.out (n := 557) f260 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 558) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 557), (10, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047e0) f260 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 559) (RestInside.out (n := 559) f261 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 560) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 557), (10, 559), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047e3) f261 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 561) (RestInside.out (n := 561) f262 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 562) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 557), (10, 561), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047e7) f262 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 563) (RestInside.out (n := 563) f263 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 564) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 557), (10, 563), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047ea) f263 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 565) (RestInside.out (n := 565) f264 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 566) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 557), (10, 565), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047f1) f264 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 567) (RestInside.out (n := 567) f265 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 568) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 567), (10, 565), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047f4) f265 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 569) (RestInside.out (n := 569) f266 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 570) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 567), (10, 569), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047f8) f266 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 571) (RestInside.out (n := 571) f267 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 572) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 567), (10, 571), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047fb) f267 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 573) (RestInside.out (n := 573) f268 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 574) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 573), (10, 571), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047fe) f268 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 575) (RestInside.out (n := 575) f269 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 576) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 575), (10, 571), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104801) f269 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 577) (RestInside.out (n := 577) f270 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 578) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 577), (10, 571), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104804) f270 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 579) (RestInside.out (n := 579) f271 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 580) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 579), (10, 571), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10480b) f271 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 581) (RestInside.out (n := 581) f272 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 582) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 579), (10, 581), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10480e) f272 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 583) (RestInside.out (n := 583) f273 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 584) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 583), (10, 581), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104811) f273 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 585) (RestInside.out (n := 585) f274 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 586) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 585), (10, 581), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104814) f274 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 587) (RestInside.exec (n := 587) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 585), (10, 581), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10481a) f275 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 588) (RestInside.out (n := 588) f276 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 589) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 588), (10, 581), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104820) f276 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 590) (RestInside.out (n := 590) f277 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 591) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 588), (10, 590), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104823) f277 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 592) (RestInside.out (n := 592) f278 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 593) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 588), (10, 592), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104827) f278 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 594) (RestInside.out (n := 594) f279 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 595) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 588), (10, 594), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10482a) f279 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_14 code

theorem rest_l10446f_12 [Bindings] (code : CodeMap) :
    Rest (n := 519) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 517), (10, 509), (22, 22), (39, 39), (50, 50), (51, 51)]
      593 0x10478b bytes_l10446f_12 b_l10446f_12 := by
  have f240 : InstrSpec 0x10478b [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x10478b) (xorR32R32Effect 0x10478b 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10478b 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10478b 0x45 0xca (by decide) (by decide)) pre_rip
  have f241 : InstrSpec 0x10478e [0x45, 0x01, 0xC9] (fun s => s.RIP = 0x10478e) (addR32R32Effect 0x10478e 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10478e 3 9 9).toInstrSpec (add_r32_r32_rex_effect_step 0x10478e 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f242 : InstrSpec 0x104791 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104791) (xorR32R32Effect 0x104791 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104791 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104791 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f243 : InstrSpec 0x104794 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x3C] (StorePre 0x104794 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x104794 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104794 6 9 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104794 6 9 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104794 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f244 : InstrSpec 0x10479a [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x3E] (LoadPre 0x10479a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x10479a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10479a 6 9 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x10479a 6 9 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10479a 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f245 : InstrSpec 0x1047a0 [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x1047a0) (movR32R32Effect 0x1047a0 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1047a0 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x1047a0 0x45 0xca (by decide) (by decide)) pre_rip
  have f246 : InstrSpec 0x1047a3 [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x1047a3) (shrR32Effect 0x1047a3 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x1047a3 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1047a3 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f247 : InstrSpec 0x1047a7 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x1047a7) (xorR32R32Effect 0x1047a7 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1047a7 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1047a7 0x45 0xca (by decide) (by decide)) pre_rip
  have f248 : InstrSpec 0x1047aa [0x41, 0x81, 0xE2, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x1047aa) (andR32Imm32Effect 0x1047aa 7 10 0x2310)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1047aa 7 10 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x1047aa 0x41 0xe2 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f249 : InstrSpec 0x1047b1 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x1047b1) (xorR32R32Effect 0x1047b1 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1047b1 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1047b1 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f250 : InstrSpec 0x1047b4 [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x1047b4) (shlR32Effect 0x1047b4 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x1047b4 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1047b4 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f251 : InstrSpec 0x1047b8 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x1047b8) (xorR32R32Effect 0x1047b8 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1047b8 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1047b8 0x45 0xca (by decide) (by decide)) pre_rip
  have f252 : InstrSpec 0x1047bb [0x45, 0x89, 0xD1] (fun s => s.RIP = 0x1047bb) (movR32R32Effect 0x1047bb 3 9 10)
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1047bb 3 9 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x1047bb 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f253 : InstrSpec 0x1047be [0x41, 0xD1, 0xE9] (fun s => s.RIP = 0x1047be) (shrR32Effect 0x1047be 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x1047be 3 9 1).toInstrSpec (shr_r32_one_rex_effect_step 0x1047be 0x41 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f254 : InstrSpec 0x1047c1 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x1047c1) (xorR32R32Effect 0x1047c1 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1047c1 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1047c1 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f255 : InstrSpec 0x1047c4 [0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1047c4) (andR32Imm32Effect 0x1047c4 7 9 0x5050)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1047c4 7 9 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x1047c4 0x41 0xe1 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f256 : InstrSpec 0x1047cb [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x1047cb) (xorR32R32Effect 0x1047cb 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1047cb 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1047cb 0x45 0xca (by decide) (by decide)) pre_rip
  have f257 : InstrSpec 0x1047ce [0x45, 0x01, 0xC9] (fun s => s.RIP = 0x1047ce) (addR32R32Effect 0x1047ce 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1047ce 3 9 9).toInstrSpec (add_r32_r32_rex_effect_step 0x1047ce 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f258 : InstrSpec 0x1047d1 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x1047d1) (xorR32R32Effect 0x1047d1 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1047d1 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1047d1 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f259 : InstrSpec 0x1047d4 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x3E] (StorePre 0x1047d4 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x1047d4 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1047d4 6 9 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1047d4 6 9 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1047d4 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 519) (RestInside.out (n := 519) f240 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 520) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 517), (10, 519), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10478e) f240 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 521) (RestInside.out (n := 521) f241 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 522) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 521), (10, 519), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104791) f241 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 523) (RestInside.out (n := 523) f242 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 524) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 523), (10, 519), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104794) f242 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 525) (RestInside.exec (n := 525) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 523), (10, 519), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10479a) f243 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 526) (RestInside.out (n := 526) f244 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 527) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 526), (10, 519), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047a0) f244 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 528) (RestInside.out (n := 528) f245 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 529) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 526), (10, 528), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047a3) f245 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 530) (RestInside.out (n := 530) f246 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 531) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 526), (10, 530), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047a7) f246 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 532) (RestInside.out (n := 532) f247 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 533) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 526), (10, 532), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047aa) f247 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 534) (RestInside.out (n := 534) f248 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 535) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 526), (10, 534), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047b1) f248 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 536) (RestInside.out (n := 536) f249 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 537) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 536), (10, 534), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047b4) f249 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 538) (RestInside.out (n := 538) f250 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 539) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 536), (10, 538), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047b8) f250 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 540) (RestInside.out (n := 540) f251 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 541) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 536), (10, 540), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047bb) f251 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 542) (RestInside.out (n := 542) f252 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 543) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 542), (10, 540), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047be) f252 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 544) (RestInside.out (n := 544) f253 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 545) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 544), (10, 540), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047c1) f253 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 546) (RestInside.out (n := 546) f254 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 547) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 546), (10, 540), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047c4) f254 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 548) (RestInside.out (n := 548) f255 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 549) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 548), (10, 540), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047cb) f255 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 550) (RestInside.out (n := 550) f256 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 551) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 548), (10, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047ce) f256 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 552) (RestInside.out (n := 552) f257 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 553) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 552), (10, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047d1) f257 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 554) (RestInside.out (n := 554) f258 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 555) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 554), (10, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047d4) f258 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 556) (RestInside.exec (n := 556) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 554), (10, 550), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1047da) f259 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10446f_13 code

theorem rest_l10446f_11 [Bindings] (code : CodeMap) :
    Rest (n := 480) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 474), (10, 478), (22, 22), (39, 39), (50, 50), (51, 51)]
      613 0x10473b bytes_l10446f_11 b_l10446f_11 := by
  have f220 : InstrSpec 0x10473b [0x45, 0x89, 0xD1] (fun s => s.RIP = 0x10473b) (movR32R32Effect 0x10473b 3 9 10)
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x10473b 3 9 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x10473b 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f221 : InstrSpec 0x10473e [0x41, 0xD1, 0xE9] (fun s => s.RIP = 0x10473e) (shrR32Effect 0x10473e 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x10473e 3 9 1).toInstrSpec (shr_r32_one_rex_effect_step 0x10473e 0x41 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f222 : InstrSpec 0x104741 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104741) (xorR32R32Effect 0x104741 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104741 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104741 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f223 : InstrSpec 0x104744 [0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104744) (andR32Imm32Effect 0x104744 7 9 0x5050)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104744 7 9 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104744 0x41 0xe1 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f224 : InstrSpec 0x10474b [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x10474b) (xorR32R32Effect 0x10474b 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10474b 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10474b 0x45 0xca (by decide) (by decide)) pre_rip
  have f225 : InstrSpec 0x10474e [0x45, 0x01, 0xC9] (fun s => s.RIP = 0x10474e) (addR32R32Effect 0x10474e 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10474e 3 9 9).toInstrSpec (add_r32_r32_rex_effect_step 0x10474e 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f226 : InstrSpec 0x104751 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104751) (xorR32R32Effect 0x104751 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104751 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104751 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f227 : InstrSpec 0x104754 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x3A] (StorePre 0x104754 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x104754 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x104754 6 9 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104754 6 9 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (mov_m16_r16_rex_effect_step 0x104754 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f228 : InstrSpec 0x10475a [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x3C] (LoadPre 0x10475a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x10475a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10475a 6 9 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x10475a 6 9 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10475a 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f229 : InstrSpec 0x104760 [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x104760) (movR32R32Effect 0x104760 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x104760 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x104760 0x45 0xca (by decide) (by decide)) pre_rip
  have f230 : InstrSpec 0x104763 [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x104763) (shrR32Effect 0x104763 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x104763 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104763 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f231 : InstrSpec 0x104767 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x104767) (xorR32R32Effect 0x104767 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104767 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104767 0x45 0xca (by decide) (by decide)) pre_rip
  have f232 : InstrSpec 0x10476a [0x41, 0x81, 0xE2, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x10476a) (andR32Imm32Effect 0x10476a 7 10 0x2310)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10476a 7 10 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x10476a 0x41 0xe2 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f233 : InstrSpec 0x104771 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104771) (xorR32R32Effect 0x104771 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104771 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104771 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f234 : InstrSpec 0x104774 [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x104774) (shlR32Effect 0x104774 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x104774 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104774 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f235 : InstrSpec 0x104778 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x104778) (xorR32R32Effect 0x104778 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104778 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104778 0x45 0xca (by decide) (by decide)) pre_rip
  have f236 : InstrSpec 0x10477b [0x45, 0x89, 0xD1] (fun s => s.RIP = 0x10477b) (movR32R32Effect 0x10477b 3 9 10)
      [.gpr 10] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x10477b 3 9 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x10477b 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f237 : InstrSpec 0x10477e [0x41, 0xD1, 0xE9] (fun s => s.RIP = 0x10477e) (shrR32Effect 0x10477e 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x10477e 3 9 1).toInstrSpec (shr_r32_one_rex_effect_step 0x10477e 0x41 0xe9 (by decide) (by decide) (by decide)) pre_rip
  have f238 : InstrSpec 0x104781 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104781) (xorR32R32Effect 0x104781 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104781 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104781 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f239 : InstrSpec 0x104784 [0x41, 0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x104784) (andR32Imm32Effect 0x104784 7 9 0x5050)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104784 7 9 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x104784 0x41 0xe1 0x5050 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 480) (RestInside.out (n := 480) f220 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 481) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 480), (10, 478), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10473e) f220 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 482) (RestInside.out (n := 482) f221 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 483) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 482), (10, 478), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104741) f221 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 484) (RestInside.out (n := 484) f222 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 485) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 484), (10, 478), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104744) f222 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 486) (RestInside.out (n := 486) f223 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 487) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 486), (10, 478), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10474b) f223 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 488) (RestInside.out (n := 488) f224 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 489) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 486), (10, 488), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10474e) f224 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 490) (RestInside.out (n := 490) f225 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 491) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 490), (10, 488), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104751) f225 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 492) (RestInside.out (n := 492) f226 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 493) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 492), (10, 488), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104754) f226 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 494) (RestInside.exec (n := 494) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 492), (10, 488), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10475a) f227 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 495) (RestInside.out (n := 495) f228 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 496) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 495), (10, 488), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104760) f228 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 497) (RestInside.out (n := 497) f229 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 498) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 495), (10, 497), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104763) f229 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 499) (RestInside.out (n := 499) f230 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 500) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 495), (10, 499), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104767) f230 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 501) (RestInside.out (n := 501) f231 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 502) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 495), (10, 501), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10476a) f231 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 503) (RestInside.out (n := 503) f232 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 504) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 495), (10, 503), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104771) f232 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 505) (RestInside.out (n := 505) f233 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 506) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 505), (10, 503), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104774) f233 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 507) (RestInside.out (n := 507) f234 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 508) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 505), (10, 507), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104778) f234 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 509) (RestInside.out (n := 509) f235 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 510) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 505), (10, 509), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10477b) f235 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 511) (RestInside.out (n := 511) f236 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 512) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 511), (10, 509), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10477e) f236 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 513) (RestInside.out (n := 513) f237 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 514) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 513), (10, 509), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104781) f237 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 515) (RestInside.out (n := 515) f238 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 516) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 515), (10, 509), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104784) f238 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 517) (RestInside.out (n := 517) f239 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 518) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 517), (10, 509), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10478b) f239 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_12 code

theorem rest_l10446f_10 [Bindings] (code : CodeMap) :
    Rest (n := 440) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 434), (9, 438), (22, 22), (39, 39), (50, 50), (51, 51)]
      633 0x1046ed bytes_l10446f_10 b_l10446f_10 := by
  have f200 : InstrSpec 0x1046ed [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x1046ed) (xorR32R32Effect 0x1046ed 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1046ed 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1046ed 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f201 : InstrSpec 0x1046f0 [0x41, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x1046f0) (andR32Imm32Effect 0x1046f0 7 9 0x2310)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1046f0 7 9 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x1046f0 0x41 0xe1 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f202 : InstrSpec 0x1046f7 [0x45, 0x31, 0xC8] (fun s => s.RIP = 0x1046f7) (xorR32R32Effect 0x1046f7 3 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1046f7 3 8 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1046f7 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f203 : InstrSpec 0x1046fa [0x41, 0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1046fa) (shlR32Effect 0x1046fa 4 9 2)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR32Effect_footprint 0x1046fa 4 9 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1046fa 0x41 0xe1 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f204 : InstrSpec 0x1046fe [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x1046fe) (xorR32R32Effect 0x1046fe 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1046fe 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1046fe 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f205 : InstrSpec 0x104701 [0x45, 0x89, 0xC8] (fun s => s.RIP = 0x104701) (movR32R32Effect 0x104701 3 8 9)
      [.gpr 9] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x104701 3 8 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x104701 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f206 : InstrSpec 0x104704 [0x41, 0xD1, 0xE8] (fun s => s.RIP = 0x104704) (shrR32Effect 0x104704 3 8 1)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x104704 3 8 1).toInstrSpec (shr_r32_one_rex_effect_step 0x104704 0x41 0xe8 (by decide) (by decide) (by decide)) pre_rip
  have f207 : InstrSpec 0x104707 [0x45, 0x31, 0xC8] (fun s => s.RIP = 0x104707) (xorR32R32Effect 0x104707 3 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104707 3 8 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104707 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f208 : InstrSpec 0x10470a [0x41, 0x81, 0xE0, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10470a) (andR32Imm32Effect 0x10470a 7 8 0x5050)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10470a 7 8 0x5050).toInstrSpec (and_r32_imm32_rex_effect_step 0x10470a 0x41 0xe0 0x5050 (by decide) (by decide) (by decide)) pre_rip
  have f209 : InstrSpec 0x104711 [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x104711) (xorR32R32Effect 0x104711 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104711 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x104711 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f210 : InstrSpec 0x104714 [0x45, 0x01, 0xC0] (fun s => s.RIP = 0x104714) (addR32R32Effect 0x104714 3 8 8)
      [.gpr 8, .gpr 8] [] [.reg 8, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104714 3 8 8).toInstrSpec (add_r32_r32_rex_effect_step 0x104714 0x45 0xc0 (by decide) (by decide)) pre_rip
  have f211 : InstrSpec 0x104717 [0x45, 0x31, 0xC8] (fun s => s.RIP = 0x104717) (xorR32R32Effect 0x104717 3 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104717 3 8 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104717 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f212 : InstrSpec 0x10471a [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x3A] (LoadPre 0x10471a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x10471a + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10471a 6 9 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x10471a 6 9 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10471a 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f213 : InstrSpec 0x104720 [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x104720) (movR32R32Effect 0x104720 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x104720 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x104720 0x45 0xca (by decide) (by decide)) pre_rip
  have f214 : InstrSpec 0x104723 [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x104723) (shrR32Effect 0x104723 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x104723 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x104723 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f215 : InstrSpec 0x104727 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x104727) (xorR32R32Effect 0x104727 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104727 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104727 0x45 0xca (by decide) (by decide)) pre_rip
  have f216 : InstrSpec 0x10472a [0x41, 0x81, 0xE2, 0x10, 0x23, 0x00, 0x00] (fun s => s.RIP = 0x10472a) (andR32Imm32Effect 0x10472a 7 10 0x2310)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10472a 7 10 0x2310).toInstrSpec (and_r32_imm32_rex_effect_step 0x10472a 0x41 0xe2 0x2310 (by decide) (by decide) (by decide)) pre_rip
  have f217 : InstrSpec 0x104731 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x104731) (xorR32R32Effect 0x104731 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104731 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104731 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f218 : InstrSpec 0x104734 [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x104734) (shlR32Effect 0x104734 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x104734 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x104734 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f219 : InstrSpec 0x104738 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x104738) (xorR32R32Effect 0x104738 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104738 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104738 0x45 0xca (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 440) (RestInside.out (n := 440) f200 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 441) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 434), (9, 440), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046f0) f200 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 442) (RestInside.out (n := 442) f201 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 443) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 434), (9, 442), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046f7) f201 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 444) (RestInside.out (n := 444) f202 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 445) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 444), (9, 442), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046fa) f202 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 446) (RestInside.out (n := 446) f203 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 447) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 444), (9, 446), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046fe) f203 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 448) (RestInside.out (n := 448) f204 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 449) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 444), (9, 448), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104701) f204 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 450) (RestInside.out (n := 450) f205 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 451) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 450), (9, 448), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104704) f205 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 452) (RestInside.out (n := 452) f206 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 453) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 452), (9, 448), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104707) f206 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 454) (RestInside.out (n := 454) f207 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 455) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 454), (9, 448), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10470a) f207 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 456) (RestInside.out (n := 456) f208 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 457) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 456), (9, 448), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104711) f208 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 458) (RestInside.out (n := 458) f209 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 459) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 456), (9, 458), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104714) f209 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 460) (RestInside.out (n := 460) f210 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 461) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 460), (9, 458), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104717) f210 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 462) (RestInside.out (n := 462) f211 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 463) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 458), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10471a) f211 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 464) (RestInside.out (n := 464) f212 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 465) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 464), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104720) f212 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 466) (RestInside.out (n := 466) f213 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 467) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 464), (10, 466), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104723) f213 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 468) (RestInside.out (n := 468) f214 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 469) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 464), (10, 468), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104727) f214 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 470) (RestInside.out (n := 470) f215 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 471) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 464), (10, 470), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10472a) f215 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 472) (RestInside.out (n := 472) f216 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 473) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 464), (10, 472), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104731) f216 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 474) (RestInside.out (n := 474) f217 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 475) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 474), (10, 472), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104734) f217 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 476) (RestInside.out (n := 476) f218 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 477) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 474), (10, 476), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104738) f218 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 478) (RestInside.out (n := 478) f219 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 479) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 462), (9, 474), (10, 478), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10473b) f219 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_11 code

theorem rest_l10446f_9 [Bindings] (code : CodeMap) :
    Rest (n := 401) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 395), (22, 22), (39, 39), (50, 50), (51, 51)]
      653 0x10469b bytes_l10446f_9 b_l10446f_9 := by
  have f180 : InstrSpec 0x10469b [0x44, 0x0F, 0xB7, 0x44, 0x24, 0x34] (LoadPre 0x10469b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x10469b + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10469b 6 8 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x10469b 6 8 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10469b 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f181 : InstrSpec 0x1046a1 [0x44, 0x89, 0xC7] (fun s => s.RIP = 0x1046a1) (movR32R32Effect 0x1046a1 3 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x1046a1 3 7 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x1046a1 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f182 : InstrSpec 0x1046a4 [0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x1046a4) (shrR32Effect 0x1046a4 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x1046a4 3 7 2).toInstrSpec (shr_r32_imm8_effect_step 0x1046a4 0xef 0x2 (by decide) (by decide)) pre_rip
  have f183 : InstrSpec 0x1046a7 [0x44, 0x31, 0xC7] (fun s => s.RIP = 0x1046a7) (xorR32R32Effect 0x1046a7 3 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1046a7 3 7 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1046a7 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f184 : InstrSpec 0x1046aa [0x81, 0xE7, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x1046aa) (andR32Imm32Effect 0x1046aa 6 7 0x3030)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1046aa 6 7 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x1046aa 0xe7 0x3030 (by decide) (by decide)) pre_rip
  have f185 : InstrSpec 0x1046b0 [0x41, 0x31, 0xF8] (fun s => s.RIP = 0x1046b0) (xorR32R32Effect 0x1046b0 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1046b0 3 8 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x1046b0 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f186 : InstrSpec 0x1046b3 [0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x1046b3) (shlR32Effect 0x1046b3 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x1046b3 3 7 2).toInstrSpec (shl_r32_imm8_effect_step 0x1046b3 0xe7 0x2 (by decide) (by decide)) pre_rip
  have f187 : InstrSpec 0x1046b6 [0x44, 0x31, 0xC7] (fun s => s.RIP = 0x1046b6) (xorR32R32Effect 0x1046b6 3 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1046b6 3 7 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1046b6 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f188 : InstrSpec 0x1046b9 [0x44, 0x0F, 0xB7, 0x44, 0x24, 0x36] (LoadPre 0x1046b9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x1046b9 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1046b9 6 8 (.sib 4 none 0 (.d8 0x36)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x1046b9 6 8 (.sib 4 none 0 (.d8 0x36))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1046b9 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f189 : InstrSpec 0x1046bf [0x45, 0x89, 0xC1] (fun s => s.RIP = 0x1046bf) (movR32R32Effect 0x1046bf 3 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1046bf 3 9 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x1046bf 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f190 : InstrSpec 0x1046c2 [0x41, 0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1046c2) (shrR32Effect 0x1046c2 4 9 2)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x1046c2 4 9 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1046c2 0x41 0xe9 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f191 : InstrSpec 0x1046c6 [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x1046c6) (xorR32R32Effect 0x1046c6 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1046c6 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1046c6 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f192 : InstrSpec 0x1046c9 [0x41, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x1046c9) (andR32Imm32Effect 0x1046c9 7 9 0x3030)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1046c9 7 9 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x1046c9 0x41 0xe1 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f193 : InstrSpec 0x1046d0 [0x45, 0x31, 0xC8] (fun s => s.RIP = 0x1046d0) (xorR32R32Effect 0x1046d0 3 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1046d0 3 8 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1046d0 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f194 : InstrSpec 0x1046d3 [0x41, 0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x1046d3) (shlR32Effect 0x1046d3 4 9 2)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR32Effect_footprint 0x1046d3 4 9 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1046d3 0x41 0xe1 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f195 : InstrSpec 0x1046d7 [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x1046d7) (xorR32R32Effect 0x1046d7 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1046d7 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1046d7 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f196 : InstrSpec 0x1046da [0x66, 0x44, 0x89, 0x4C, 0x24, 0x36] (StorePre 0x1046da 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x1046da + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1046da 6 9 (.sib 4 none 0 (.d8 0x36)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1046da 6 9 (.sib 4 none 0 (.d8 0x36))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1046da 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f197 : InstrSpec 0x1046e0 [0x44, 0x0F, 0xB7, 0x44, 0x24, 0x38] (LoadPre 0x1046e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1046e0 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1046e0 6 8 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x1046e0 6 8 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1046e0 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f198 : InstrSpec 0x1046e6 [0x45, 0x89, 0xC1] (fun s => s.RIP = 0x1046e6) (movR32R32Effect 0x1046e6 3 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x1046e6 3 9 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x1046e6 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f199 : InstrSpec 0x1046e9 [0x41, 0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x1046e9) (shrR32Effect 0x1046e9 4 9 2)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x1046e9 4 9 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x1046e9 0x41 0xe9 0x2 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 401) (RestInside.out (n := 401) f180 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 402) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 395), (8, 401), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046a1) f180 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 403) (RestInside.out (n := 403) f181 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 404) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 403), (8, 401), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046a4) f181 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 405) (RestInside.out (n := 405) f182 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 406) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 405), (8, 401), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046a7) f182 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 407) (RestInside.out (n := 407) f183 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 408) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 407), (8, 401), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046aa) f183 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 409) (RestInside.out (n := 409) f184 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 410) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 409), (8, 401), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046b0) f184 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 411) (RestInside.out (n := 411) f185 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 412) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 409), (8, 411), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046b3) f185 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 413) (RestInside.out (n := 413) f186 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 414) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 413), (8, 411), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046b6) f186 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 415) (RestInside.out (n := 415) f187 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 416) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 411), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046b9) f187 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 417) (RestInside.out (n := 417) f188 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 418) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 417), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046bf) f188 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 419) (RestInside.out (n := 419) f189 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 420) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 417), (9, 419), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046c2) f189 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 421) (RestInside.out (n := 421) f190 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 422) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 417), (9, 421), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046c6) f190 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 423) (RestInside.out (n := 423) f191 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 424) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 417), (9, 423), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046c9) f191 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 425) (RestInside.out (n := 425) f192 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 426) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 417), (9, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046d0) f192 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 427) (RestInside.out (n := 427) f193 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 428) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 427), (9, 425), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046d3) f193 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 429) (RestInside.out (n := 429) f194 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 430) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 427), (9, 429), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046d7) f194 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 431) (RestInside.out (n := 431) f195 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 432) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 427), (9, 431), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046da) f195 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 433) (RestInside.exec (n := 433) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 427), (9, 431), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046e0) f196 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 434) (RestInside.out (n := 434) f197 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 435) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 434), (9, 431), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046e6) f197 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 436) (RestInside.out (n := 436) f198 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 437) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 434), (9, 436), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046e9) f198 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 438) (RestInside.out (n := 438) f199 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 439) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 415), (8, 434), (9, 438), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1046ed) f199 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_10 code

theorem rest_l10446f_8 [Bindings] (code : CodeMap) :
    Rest (n := 363) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 332), (2, 311), (4, 4), (6, 361), (7, 359), (22, 22), (39, 39), (50, 50), (51, 51)]
      673 0x10465a bytes_l10446f_8 b_l10446f_8 := by
  have f160 : InstrSpec 0x10465a [0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x10465a) (shlR32Effect 0x10465a 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10465a 3 7 2).toInstrSpec (shl_r32_imm8_effect_step 0x10465a 0xe7 0x2 (by decide) (by decide)) pre_rip
  have f161 : InstrSpec 0x10465d [0x31, 0xF7] (fun s => s.RIP = 0x10465d) (xorR32R32Effect 0x10465d 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10465d 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x10465d 0xf7 (by decide)) pre_rip
  have f162 : InstrSpec 0x10465f [0x66, 0x89, 0x7C, 0x24, 0x2E] (StorePre 0x10465f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x10465f + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10465f 5 7 (.sib 4 none 0 (.d8 0x2e)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10465f 5 7 (.sib 4 none 0 (.d8 0x2e))).toInstrSpec (mov_m16_r16_effect_step 0x10465f 7 (.sib 4 none 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f163 : InstrSpec 0x104664 [0x0F, 0xB7, 0x74, 0x24, 0x30] (LoadPre 0x104664 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x104664 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104664 5 6 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x104664 5 6 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (movzx_r32_m16_effect_step 0x104664 6 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f164 : InstrSpec 0x104669 [0x89, 0xF7] (fun s => s.RIP = 0x104669) (movR32R32Effect 0x104669 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x104669 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x104669 0xf7 (by decide)) pre_rip
  have f165 : InstrSpec 0x10466b [0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x10466b) (shrR32Effect 0x10466b 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x10466b 3 7 2).toInstrSpec (shr_r32_imm8_effect_step 0x10466b 0xef 0x2 (by decide) (by decide)) pre_rip
  have f166 : InstrSpec 0x10466e [0x31, 0xF7] (fun s => s.RIP = 0x10466e) (xorR32R32Effect 0x10466e 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10466e 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x10466e 0xf7 (by decide)) pre_rip
  have f167 : InstrSpec 0x104670 [0x81, 0xE7, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104670) (andR32Imm32Effect 0x104670 6 7 0x3030)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104670 6 7 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x104670 0xe7 0x3030 (by decide) (by decide)) pre_rip
  have f168 : InstrSpec 0x104676 [0x31, 0xFE] (fun s => s.RIP = 0x104676) (xorR32R32Effect 0x104676 2 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104676 2 6 7).toInstrSpec (xor_r32_r32_effect_step 0x104676 0xfe (by decide)) pre_rip
  have f169 : InstrSpec 0x104678 [0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x104678) (shlR32Effect 0x104678 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x104678 3 7 2).toInstrSpec (shl_r32_imm8_effect_step 0x104678 0xe7 0x2 (by decide) (by decide)) pre_rip
  have f170 : InstrSpec 0x10467b [0x31, 0xF7] (fun s => s.RIP = 0x10467b) (xorR32R32Effect 0x10467b 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10467b 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x10467b 0xf7 (by decide)) pre_rip
  have f171 : InstrSpec 0x10467d [0x66, 0x89, 0x7C, 0x24, 0x30] (StorePre 0x10467d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10467d + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10467d 5 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10467d 5 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m16_r16_effect_step 0x10467d 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f172 : InstrSpec 0x104682 [0x0F, 0xB7, 0x7C, 0x24, 0x32] (LoadPre 0x104682 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x104682 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104682 5 7 (.sib 4 none 0 (.d8 0x32)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x104682 5 7 (.sib 4 none 0 (.d8 0x32))).toInstrSpec (movzx_r32_m16_effect_step 0x104682 7 (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f173 : InstrSpec 0x104687 [0x89, 0xFE] (fun s => s.RIP = 0x104687) (movR32R32Effect 0x104687 2 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x104687 2 6 7).toInstrSpec (mov_r32_r32_effect_step 0x104687 0xfe (by decide)) pre_rip
  have f174 : InstrSpec 0x104689 [0xC1, 0xEE, 0x02] (fun s => s.RIP = 0x104689) (shrR32Effect 0x104689 3 6 2)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x104689 3 6 2).toInstrSpec (shr_r32_imm8_effect_step 0x104689 0xee 0x2 (by decide) (by decide)) pre_rip
  have f175 : InstrSpec 0x10468c [0x31, 0xFE] (fun s => s.RIP = 0x10468c) (xorR32R32Effect 0x10468c 2 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10468c 2 6 7).toInstrSpec (xor_r32_r32_effect_step 0x10468c 0xfe (by decide)) pre_rip
  have f176 : InstrSpec 0x10468e [0x81, 0xE6, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x10468e) (andR32Imm32Effect 0x10468e 6 6 0x3030)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10468e 6 6 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x10468e 0xe6 0x3030 (by decide) (by decide)) pre_rip
  have f177 : InstrSpec 0x104694 [0x31, 0xF7] (fun s => s.RIP = 0x104694) (xorR32R32Effect 0x104694 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104694 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x104694 0xf7 (by decide)) pre_rip
  have f178 : InstrSpec 0x104696 [0xC1, 0xE6, 0x02] (fun s => s.RIP = 0x104696) (shlR32Effect 0x104696 3 6 2)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR32Effect_footprint 0x104696 3 6 2).toInstrSpec (shl_r32_imm8_effect_step 0x104696 0xe6 0x2 (by decide) (by decide)) pre_rip
  have f179 : InstrSpec 0x104699 [0x31, 0xFE] (fun s => s.RIP = 0x104699) (xorR32R32Effect 0x104699 2 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104699 2 6 7).toInstrSpec (xor_r32_r32_effect_step 0x104699 0xfe (by decide)) pre_rip
  refine Rest.ofInside (n := 363) (RestInside.out (n := 363) f160 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 364) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 361), (7, 363), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10465d) f160 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 365) (RestInside.out (n := 365) f161 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 366) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 361), (7, 365), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10465f) f161 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 367) (RestInside.exec (n := 367) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 361), (7, 365), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104664) f162 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 368) (RestInside.out (n := 368) f163 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 369) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 368), (7, 365), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104669) f163 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 370) (RestInside.out (n := 370) f164 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 371) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 368), (7, 370), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10466b) f164 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 372) (RestInside.out (n := 372) f165 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 373) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 368), (7, 372), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10466e) f165 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 374) (RestInside.out (n := 374) f166 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 375) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 368), (7, 374), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104670) f166 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 376) (RestInside.out (n := 376) f167 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 377) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 368), (7, 376), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104676) f167 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 378) (RestInside.out (n := 378) f168 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 379) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 378), (7, 376), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104678) f168 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 380) (RestInside.out (n := 380) f169 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 381) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 378), (7, 380), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10467b) f169 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 382) (RestInside.out (n := 382) f170 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 383) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 378), (7, 382), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10467d) f170 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 384) (RestInside.exec (n := 384) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 378), (7, 382), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104682) f171 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 385) (RestInside.out (n := 385) f172 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 386) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 378), (7, 385), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104687) f172 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 387) (RestInside.out (n := 387) f173 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 388) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 387), (7, 385), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104689) f173 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 389) (RestInside.out (n := 389) f174 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 390) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 389), (7, 385), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10468c) f174 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 391) (RestInside.out (n := 391) f175 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 392) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 391), (7, 385), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10468e) f175 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 393) (RestInside.out (n := 393) f176 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 394) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 393), (7, 385), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104694) f176 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 395) (RestInside.out (n := 395) f177 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 396) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 393), (7, 395), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104696) f177 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 397) (RestInside.out (n := 397) f178 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 398) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 397), (7, 395), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104699) f178 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 399) (RestInside.out (n := 399) f179 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 400) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 399), (7, 395), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10469b) f179 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_9 code

theorem rest_l10446f_7 [Bindings] (code : CodeMap) :
    Rest (n := 324) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 315), (1, 322), (2, 311), (4, 4), (6, 318), (22, 22), (39, 39), (50, 50), (51, 51)]
      693 0x104619 bytes_l10446f_7 b_l10446f_7 := by
  have f140 : InstrSpec 0x104619 [0x31, 0xF1] (fun s => s.RIP = 0x104619) (xorR32R32Effect 0x104619 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104619 2 1 6).toInstrSpec (xor_r32_r32_effect_step 0x104619 0xf1 (by decide)) pre_rip
  have f141 : InstrSpec 0x10461b [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x10461b) (andR32Imm32Effect 0x10461b 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10461b 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x10461b 0xe1 0x3030 (by decide) (by decide)) pre_rip
  have f142 : InstrSpec 0x104621 [0x31, 0xCE] (fun s => s.RIP = 0x104621) (xorR32R32Effect 0x104621 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104621 2 6 1).toInstrSpec (xor_r32_r32_effect_step 0x104621 0xce (by decide)) pre_rip
  have f143 : InstrSpec 0x104623 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x104623) (shlR32Effect 0x104623 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x104623 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x104623 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f144 : InstrSpec 0x104626 [0x31, 0xF1] (fun s => s.RIP = 0x104626) (xorR32R32Effect 0x104626 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104626 2 1 6).toInstrSpec (xor_r32_r32_effect_step 0x104626 0xf1 (by decide)) pre_rip
  have f145 : InstrSpec 0x104628 [0x0F, 0xB7, 0x74, 0x24, 0x2C] (LoadPre 0x104628 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x104628 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104628 5 6 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x104628 5 6 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (movzx_r32_m16_effect_step 0x104628 6 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f146 : InstrSpec 0x10462d [0x89, 0xF7] (fun s => s.RIP = 0x10462d) (movR32R32Effect 0x10462d 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x10462d 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x10462d 0xf7 (by decide)) pre_rip
  have f147 : InstrSpec 0x10462f [0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x10462f) (shrR32Effect 0x10462f 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x10462f 3 7 2).toInstrSpec (shr_r32_imm8_effect_step 0x10462f 0xef 0x2 (by decide) (by decide)) pre_rip
  have f148 : InstrSpec 0x104632 [0x31, 0xF7] (fun s => s.RIP = 0x104632) (xorR32R32Effect 0x104632 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104632 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x104632 0xf7 (by decide)) pre_rip
  have f149 : InstrSpec 0x104634 [0x81, 0xE7, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104634) (andR32Imm32Effect 0x104634 6 7 0x3030)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104634 6 7 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x104634 0xe7 0x3030 (by decide) (by decide)) pre_rip
  have f150 : InstrSpec 0x10463a [0x31, 0xFE] (fun s => s.RIP = 0x10463a) (xorR32R32Effect 0x10463a 2 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10463a 2 6 7).toInstrSpec (xor_r32_r32_effect_step 0x10463a 0xfe (by decide)) pre_rip
  have f151 : InstrSpec 0x10463c [0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x10463c) (shlR32Effect 0x10463c 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10463c 3 7 2).toInstrSpec (shl_r32_imm8_effect_step 0x10463c 0xe7 0x2 (by decide) (by decide)) pre_rip
  have f152 : InstrSpec 0x10463f [0x31, 0xF7] (fun s => s.RIP = 0x10463f) (xorR32R32Effect 0x10463f 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10463f 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x10463f 0xf7 (by decide)) pre_rip
  have f153 : InstrSpec 0x104641 [0x66, 0x89, 0x7C, 0x24, 0x2C] (StorePre 0x104641 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x104641 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104641 5 7 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x104641 5 7 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_m16_r16_effect_step 0x104641 7 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f154 : InstrSpec 0x104646 [0x0F, 0xB7, 0x74, 0x24, 0x2E] (LoadPre 0x104646 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x104646 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104646 5 6 (.sib 4 none 0 (.d8 0x2e)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x104646 5 6 (.sib 4 none 0 (.d8 0x2e))).toInstrSpec (movzx_r32_m16_effect_step 0x104646 6 (.sib 4 none 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f155 : InstrSpec 0x10464b [0x89, 0xF7] (fun s => s.RIP = 0x10464b) (movR32R32Effect 0x10464b 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x10464b 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x10464b 0xf7 (by decide)) pre_rip
  have f156 : InstrSpec 0x10464d [0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x10464d) (shrR32Effect 0x10464d 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x10464d 3 7 2).toInstrSpec (shr_r32_imm8_effect_step 0x10464d 0xef 0x2 (by decide) (by decide)) pre_rip
  have f157 : InstrSpec 0x104650 [0x31, 0xF7] (fun s => s.RIP = 0x104650) (xorR32R32Effect 0x104650 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104650 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x104650 0xf7 (by decide)) pre_rip
  have f158 : InstrSpec 0x104652 [0x81, 0xE7, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x104652) (andR32Imm32Effect 0x104652 6 7 0x3030)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104652 6 7 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x104652 0xe7 0x3030 (by decide) (by decide)) pre_rip
  have f159 : InstrSpec 0x104658 [0x31, 0xFE] (fun s => s.RIP = 0x104658) (xorR32R32Effect 0x104658 2 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104658 2 6 7).toInstrSpec (xor_r32_r32_effect_step 0x104658 0xfe (by decide)) pre_rip
  refine Rest.ofInside (n := 324) (RestInside.out (n := 324) f140 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 325) (ρ' := [(0, 315), (1, 324), (2, 311), (4, 4), (6, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10461b) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 326) (RestInside.out (n := 326) f141 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 327) (ρ' := [(0, 315), (1, 326), (2, 311), (4, 4), (6, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104621) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 328) (RestInside.out (n := 328) f142 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 329) (ρ' := [(0, 315), (1, 326), (2, 311), (4, 4), (6, 328), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104623) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 330) (RestInside.out (n := 330) f143 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 331) (ρ' := [(0, 315), (1, 330), (2, 311), (4, 4), (6, 328), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104626) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 332) (RestInside.out (n := 332) f144 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 333) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 328), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104628) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 334) (RestInside.out (n := 334) f145 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 335) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 334), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10462d) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 336) (RestInside.out (n := 336) f146 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 337) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 334), (7, 336), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10462f) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 338) (RestInside.out (n := 338) f147 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 339) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 334), (7, 338), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104632) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 340) (RestInside.out (n := 340) f148 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 341) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 334), (7, 340), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104634) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 342) (RestInside.out (n := 342) f149 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 343) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 334), (7, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10463a) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 344) (RestInside.out (n := 344) f150 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 345) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 344), (7, 342), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10463c) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 346) (RestInside.out (n := 346) f151 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 347) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 344), (7, 346), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10463f) f151 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 348) (RestInside.out (n := 348) f152 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 349) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 344), (7, 348), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104641) f152 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 350) (RestInside.exec (n := 350) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 344), (7, 348), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104646) f153 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 351) (RestInside.out (n := 351) f154 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 352) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 351), (7, 348), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10464b) f154 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 353) (RestInside.out (n := 353) f155 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 354) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 351), (7, 353), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10464d) f155 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 355) (RestInside.out (n := 355) f156 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 356) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 351), (7, 355), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104650) f156 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 357) (RestInside.out (n := 357) f157 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 358) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 351), (7, 357), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104652) f157 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 359) (RestInside.out (n := 359) f158 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 360) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 351), (7, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104658) f158 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 361) (RestInside.out (n := 361) f159 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 362) (ρ' := [(0, 315), (1, 332), (2, 311), (4, 4), (6, 361), (7, 359), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10465a) f159 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_8 code

theorem rest_l10446f_6 [Bindings] (code : CodeMap) :
    Rest (n := 286) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 81), (1, 280), (2, 284), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      713 0x1045d9 bytes_l10446f_6 b_l10446f_6 := by
  have f120 : InstrSpec 0x1045d9 [0x89, 0xD1] (fun s => s.RIP = 0x1045d9) (movR32R32Effect 0x1045d9 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1045d9 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x1045d9 0xd1 (by decide)) pre_rip
  have f121 : InstrSpec 0x1045db [0xD1, 0xE9] (fun s => s.RIP = 0x1045db) (shrR32Effect 0x1045db 2 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1045db 2 1 1).toInstrSpec (shr_r32_one_effect_step 0x1045db 0xe9 (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x1045dd [0x31, 0xD1] (fun s => s.RIP = 0x1045dd) (xorR32R32Effect 0x1045dd 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045dd 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1045dd 0xd1 (by decide)) pre_rip
  have f123 : InstrSpec 0x1045df [0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1045df) (andR32Imm32Effect 0x1045df 6 1 0x5050)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1045df 6 1 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x1045df 0xe1 0x5050 (by decide) (by decide)) pre_rip
  have f124 : InstrSpec 0x1045e5 [0x31, 0xCA] (fun s => s.RIP = 0x1045e5) (xorR32R32Effect 0x1045e5 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045e5 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1045e5 0xca (by decide)) pre_rip
  have f125 : InstrSpec 0x1045e7 [0x01, 0xC9] (fun s => s.RIP = 0x1045e7) (addR32R32Effect 0x1045e7 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1045e7 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x1045e7 0xc9 (by decide)) pre_rip
  have f126 : InstrSpec 0x1045e9 [0x31, 0xD1] (fun s => s.RIP = 0x1045e9) (xorR32R32Effect 0x1045e9 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045e9 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1045e9 0xd1 (by decide)) pre_rip
  have f127 : InstrSpec 0x1045eb [0x66, 0x89, 0x4C, 0x24, 0x26] (StorePre 0x1045eb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x1045eb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1045eb 5 1 (.sib 4 none 0 (.d8 0x26)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1045eb 5 1 (.sib 4 none 0 (.d8 0x26))).toInstrSpec (mov_m16_r16_effect_step 0x1045eb 1 (.sib 4 none 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f128 : InstrSpec 0x1045f0 [0x0F, 0xB7, 0x54, 0x24, 0x28] (LoadPre 0x1045f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1045f0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1045f0 5 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x1045f0 5 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m16_effect_step 0x1045f0 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f129 : InstrSpec 0x1045f5 [0x89, 0xD0] (fun s => s.RIP = 0x1045f5) (movR32R32Effect 0x1045f5 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1045f5 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x1045f5 0xd0 (by decide)) pre_rip
  have f130 : InstrSpec 0x1045f7 [0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x1045f7) (shrR32Effect 0x1045f7 3 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x1045f7 3 0 2).toInstrSpec (shr_r32_imm8_effect_step 0x1045f7 0xe8 0x2 (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x1045fa [0x31, 0xD0] (fun s => s.RIP = 0x1045fa) (xorR32R32Effect 0x1045fa 2 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045fa 2 0 2).toInstrSpec (xor_r32_r32_effect_step 0x1045fa 0xd0 (by decide)) pre_rip
  have f132 : InstrSpec 0x1045fc [0x25, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x1045fc) (andEaxImm32Effect 0x1045fc 0x3030)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1045fc 0x3030).toInstrSpec (and_eax_imm32_effect_step 0x1045fc 0x3030) pre_rip
  have f133 : InstrSpec 0x104601 [0x31, 0xC2] (fun s => s.RIP = 0x104601) (xorR32R32Effect 0x104601 2 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104601 2 2 0).toInstrSpec (xor_r32_r32_effect_step 0x104601 0xc2 (by decide)) pre_rip
  have f134 : InstrSpec 0x104603 [0xC1, 0xE0, 0x02] (fun s => s.RIP = 0x104603) (shlR32Effect 0x104603 3 0 2)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x104603 3 0 2).toInstrSpec (shl_r32_imm8_effect_step 0x104603 0xe0 0x2 (by decide) (by decide)) pre_rip
  have f135 : InstrSpec 0x104606 [0x31, 0xD0] (fun s => s.RIP = 0x104606) (xorR32R32Effect 0x104606 2 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104606 2 0 2).toInstrSpec (xor_r32_r32_effect_step 0x104606 0xd0 (by decide)) pre_rip
  have f136 : InstrSpec 0x104608 [0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x104608 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x104608 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x104608 0 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x104608 0 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m32_r32_low_effect_step 0x104608 0 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f137 : InstrSpec 0x10460f [0x0F, 0xB7, 0x74, 0x24, 0x2A] (LoadPre 0x10460f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x10460f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10460f 5 6 (.sib 4 none 0 (.d8 0x2a)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x10460f 5 6 (.sib 4 none 0 (.d8 0x2a))).toInstrSpec (movzx_r32_m16_effect_step 0x10460f 6 (.sib 4 none 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f138 : InstrSpec 0x104614 [0x89, 0xF1] (fun s => s.RIP = 0x104614) (movR32R32Effect 0x104614 2 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x104614 2 1 6).toInstrSpec (mov_r32_r32_effect_step 0x104614 0xf1 (by decide)) pre_rip
  have f139 : InstrSpec 0x104616 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x104616) (shrR32Effect 0x104616 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x104616 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x104616 0xe9 0x2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 286) (RestInside.out (n := 286) f120 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 287) (ρ' := [(0, 81), (1, 286), (2, 284), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045db) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 288) (RestInside.out (n := 288) f121 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 289) (ρ' := [(0, 81), (1, 288), (2, 284), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045dd) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 290) (RestInside.out (n := 290) f122 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 291) (ρ' := [(0, 81), (1, 290), (2, 284), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045df) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 292) (RestInside.out (n := 292) f123 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 293) (ρ' := [(0, 81), (1, 292), (2, 284), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045e5) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 294) (RestInside.out (n := 294) f124 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 295) (ρ' := [(0, 81), (1, 292), (2, 294), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045e7) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 296) (RestInside.out (n := 296) f125 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 297) (ρ' := [(0, 81), (1, 296), (2, 294), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045e9) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f126 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 81), (1, 298), (2, 294), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045eb) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.exec (n := 300) (ρ' := [(0, 81), (1, 298), (2, 294), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045f0) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 301) (RestInside.out (n := 301) f128 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 302) (ρ' := [(0, 81), (1, 298), (2, 301), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045f5) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 303) (RestInside.out (n := 303) f129 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 304) (ρ' := [(0, 303), (1, 298), (2, 301), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045f7) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 305) (RestInside.out (n := 305) f130 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 306) (ρ' := [(0, 305), (1, 298), (2, 301), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045fa) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f131 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 308) (ρ' := [(0, 307), (1, 298), (2, 301), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045fc) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f132 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 309), (1, 298), (2, 301), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104601) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f133 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 312) (ρ' := [(0, 309), (1, 298), (2, 311), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104603) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f134 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 314) (ρ' := [(0, 313), (1, 298), (2, 311), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104606) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 315) (RestInside.out (n := 315) f135 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 316) (ρ' := [(0, 315), (1, 298), (2, 311), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104608) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 317) (RestInside.exec (n := 317) (ρ' := [(0, 315), (1, 298), (2, 311), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10460f) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 318) (RestInside.out (n := 318) f137 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 319) (ρ' := [(0, 315), (1, 298), (2, 311), (4, 4), (6, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104614) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 320) (RestInside.out (n := 320) f138 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 321) (ρ' := [(0, 315), (1, 320), (2, 311), (4, 4), (6, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104616) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f139 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 323) (ρ' := [(0, 315), (1, 322), (2, 311), (4, 4), (6, 318), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104619) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_7 code

theorem rest_l10446f_5 [Bindings] (code : CodeMap) :
    Rest (n := 247) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 81), (1, 239), (2, 245), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      733 0x10459c bytes_l10446f_5 b_l10446f_5 := by
  have f100 : InstrSpec 0x10459c [0x81, 0xE2, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10459c) (andR32Imm32Effect 0x10459c 6 2 0x1320)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10459c 6 2 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x10459c 0xe2 0x1320 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x1045a2 [0x31, 0xD1] (fun s => s.RIP = 0x1045a2) (xorR32R32Effect 0x1045a2 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045a2 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1045a2 0xd1 (by decide)) pre_rip
  have f102 : InstrSpec 0x1045a4 [0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x1045a4) (shlR32Effect 0x1045a4 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x1045a4 3 2 2).toInstrSpec (shl_r32_imm8_effect_step 0x1045a4 0xe2 0x2 (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x1045a7 [0x31, 0xCA] (fun s => s.RIP = 0x1045a7) (xorR32R32Effect 0x1045a7 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045a7 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1045a7 0xca (by decide)) pre_rip
  have f104 : InstrSpec 0x1045a9 [0x89, 0xD1] (fun s => s.RIP = 0x1045a9) (movR32R32Effect 0x1045a9 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1045a9 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x1045a9 0xd1 (by decide)) pre_rip
  have f105 : InstrSpec 0x1045ab [0xD1, 0xE9] (fun s => s.RIP = 0x1045ab) (shrR32Effect 0x1045ab 2 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1045ab 2 1 1).toInstrSpec (shr_r32_one_effect_step 0x1045ab 0xe9 (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x1045ad [0x31, 0xD1] (fun s => s.RIP = 0x1045ad) (xorR32R32Effect 0x1045ad 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045ad 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1045ad 0xd1 (by decide)) pre_rip
  have f107 : InstrSpec 0x1045af [0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1045af) (andR32Imm32Effect 0x1045af 6 1 0x5050)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1045af 6 1 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x1045af 0xe1 0x5050 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x1045b5 [0x31, 0xCA] (fun s => s.RIP = 0x1045b5) (xorR32R32Effect 0x1045b5 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045b5 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1045b5 0xca (by decide)) pre_rip
  have f109 : InstrSpec 0x1045b7 [0x01, 0xC9] (fun s => s.RIP = 0x1045b7) (addR32R32Effect 0x1045b7 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1045b7 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x1045b7 0xc9 (by decide)) pre_rip
  have f110 : InstrSpec 0x1045b9 [0x31, 0xD1] (fun s => s.RIP = 0x1045b9) (xorR32R32Effect 0x1045b9 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045b9 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1045b9 0xd1 (by decide)) pre_rip
  have f111 : InstrSpec 0x1045bb [0x66, 0x89, 0x4C, 0x24, 0x24] (StorePre 0x1045bb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1045bb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1045bb 5 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1045bb 5 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_m16_r16_effect_step 0x1045bb 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f112 : InstrSpec 0x1045c0 [0x0F, 0xB7, 0x4C, 0x24, 0x26] (LoadPre 0x1045c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x1045c0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1045c0 5 1 (.sib 4 none 0 (.d8 0x26)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x1045c0 5 1 (.sib 4 none 0 (.d8 0x26))).toInstrSpec (movzx_r32_m16_effect_step 0x1045c0 1 (.sib 4 none 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f113 : InstrSpec 0x1045c5 [0x89, 0xCA] (fun s => s.RIP = 0x1045c5) (movR32R32Effect 0x1045c5 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1045c5 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x1045c5 0xca (by decide)) pre_rip
  have f114 : InstrSpec 0x1045c7 [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x1045c7) (shrR32Effect 0x1045c7 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x1045c7 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x1045c7 0xea 0x2 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x1045ca [0x31, 0xCA] (fun s => s.RIP = 0x1045ca) (xorR32R32Effect 0x1045ca 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045ca 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1045ca 0xca (by decide)) pre_rip
  have f116 : InstrSpec 0x1045cc [0x81, 0xE2, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1045cc) (andR32Imm32Effect 0x1045cc 6 2 0x1320)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1045cc 6 2 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1045cc 0xe2 0x1320 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x1045d2 [0x31, 0xD1] (fun s => s.RIP = 0x1045d2) (xorR32R32Effect 0x1045d2 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045d2 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1045d2 0xd1 (by decide)) pre_rip
  have f118 : InstrSpec 0x1045d4 [0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x1045d4) (shlR32Effect 0x1045d4 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x1045d4 3 2 2).toInstrSpec (shl_r32_imm8_effect_step 0x1045d4 0xe2 0x2 (by decide) (by decide)) pre_rip
  have f119 : InstrSpec 0x1045d7 [0x31, 0xCA] (fun s => s.RIP = 0x1045d7) (xorR32R32Effect 0x1045d7 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1045d7 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1045d7 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f100 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 81), (1, 239), (2, 247), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045a2) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f101 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 81), (1, 249), (2, 247), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045a4) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f102 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 81), (1, 249), (2, 251), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045a7) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f103 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 81), (1, 249), (2, 253), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045a9) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f104 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 81), (1, 255), (2, 253), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045ab) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f105 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 81), (1, 257), (2, 253), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045ad) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f106 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 81), (1, 259), (2, 253), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045af) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f107 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 81), (1, 261), (2, 253), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045b5) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f108 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 81), (1, 261), (2, 263), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045b7) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f109 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 81), (1, 265), (2, 263), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045b9) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f110 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 81), (1, 267), (2, 263), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045bb) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.exec (n := 269) (ρ' := [(0, 81), (1, 267), (2, 263), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045c0) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f112 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 81), (1, 270), (2, 263), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045c5) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f113 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 81), (1, 270), (2, 272), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045c7) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f114 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 81), (1, 270), (2, 274), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045ca) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f115 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 81), (1, 270), (2, 276), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045cc) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f116 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 81), (1, 270), (2, 278), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045d2) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f117 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 81), (1, 280), (2, 278), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045d4) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.out (n := 282) f118 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 283) (ρ' := [(0, 81), (1, 280), (2, 282), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045d7) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 284) (RestInside.out (n := 284) f119 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 285) (ρ' := [(0, 81), (1, 280), (2, 284), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1045d9) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_6 code

theorem rest_l10446f_4 [Bindings] (code : CodeMap) :
    Rest (n := 208) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 81), (1, 205), (2, 201), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      753 0x104560 bytes_l10446f_4 b_l10446f_4 := by
  have f80 : InstrSpec 0x104560 [0x0F, 0xB7, 0x4C, 0x24, 0x22] (LoadPre 0x104560 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x104560 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104560 5 1 (.sib 4 none 0 (.d8 0x22)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x104560 5 1 (.sib 4 none 0 (.d8 0x22))).toInstrSpec (movzx_r32_m16_effect_step 0x104560 1 (.sib 4 none 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f81 : InstrSpec 0x104565 [0x89, 0xCA] (fun s => s.RIP = 0x104565) (movR32R32Effect 0x104565 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x104565 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x104565 0xca (by decide)) pre_rip
  have f82 : InstrSpec 0x104567 [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x104567) (shrR32Effect 0x104567 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x104567 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x104567 0xea 0x2 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x10456a [0x31, 0xCA] (fun s => s.RIP = 0x10456a) (xorR32R32Effect 0x10456a 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10456a 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x10456a 0xca (by decide)) pre_rip
  have f84 : InstrSpec 0x10456c [0x81, 0xE2, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10456c) (andR32Imm32Effect 0x10456c 6 2 0x1320)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10456c 6 2 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x10456c 0xe2 0x1320 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x104572 [0x31, 0xD1] (fun s => s.RIP = 0x104572) (xorR32R32Effect 0x104572 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104572 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x104572 0xd1 (by decide)) pre_rip
  have f86 : InstrSpec 0x104574 [0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x104574) (shlR32Effect 0x104574 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x104574 3 2 2).toInstrSpec (shl_r32_imm8_effect_step 0x104574 0xe2 0x2 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x104577 [0x31, 0xCA] (fun s => s.RIP = 0x104577) (xorR32R32Effect 0x104577 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104577 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x104577 0xca (by decide)) pre_rip
  have f88 : InstrSpec 0x104579 [0x89, 0xD1] (fun s => s.RIP = 0x104579) (movR32R32Effect 0x104579 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x104579 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x104579 0xd1 (by decide)) pre_rip
  have f89 : InstrSpec 0x10457b [0xD1, 0xE9] (fun s => s.RIP = 0x10457b) (shrR32Effect 0x10457b 2 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10457b 2 1 1).toInstrSpec (shr_r32_one_effect_step 0x10457b 0xe9 (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x10457d [0x31, 0xD1] (fun s => s.RIP = 0x10457d) (xorR32R32Effect 0x10457d 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10457d 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x10457d 0xd1 (by decide)) pre_rip
  have f91 : InstrSpec 0x10457f [0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10457f) (andR32Imm32Effect 0x10457f 6 1 0x5050)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10457f 6 1 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x10457f 0xe1 0x5050 (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x104585 [0x31, 0xCA] (fun s => s.RIP = 0x104585) (xorR32R32Effect 0x104585 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104585 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x104585 0xca (by decide)) pre_rip
  have f93 : InstrSpec 0x104587 [0x01, 0xC9] (fun s => s.RIP = 0x104587) (addR32R32Effect 0x104587 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104587 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x104587 0xc9 (by decide)) pre_rip
  have f94 : InstrSpec 0x104589 [0x31, 0xD1] (fun s => s.RIP = 0x104589) (xorR32R32Effect 0x104589 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104589 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x104589 0xd1 (by decide)) pre_rip
  have f95 : InstrSpec 0x10458b [0x66, 0x89, 0x4C, 0x24, 0x22] (StorePre 0x10458b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x10458b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10458b 5 1 (.sib 4 none 0 (.d8 0x22)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10458b 5 1 (.sib 4 none 0 (.d8 0x22))).toInstrSpec (mov_m16_r16_effect_step 0x10458b 1 (.sib 4 none 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f96 : InstrSpec 0x104590 [0x0F, 0xB7, 0x4C, 0x24, 0x24] (LoadPre 0x104590 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x104590 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104590 5 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x104590 5 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (movzx_r32_m16_effect_step 0x104590 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x104595 [0x89, 0xCA] (fun s => s.RIP = 0x104595) (movR32R32Effect 0x104595 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x104595 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x104595 0xca (by decide)) pre_rip
  have f98 : InstrSpec 0x104597 [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x104597) (shrR32Effect 0x104597 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x104597 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x104597 0xea 0x2 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x10459a [0x31, 0xCA] (fun s => s.RIP = 0x10459a) (xorR32R32Effect 0x10459a 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10459a 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x10459a 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f80 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 81), (1, 208), (2, 201), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104565) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f81 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 81), (1, 208), (2, 210), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104567) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f82 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 81), (1, 208), (2, 212), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10456a) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f83 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 81), (1, 208), (2, 214), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10456c) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f84 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 81), (1, 208), (2, 216), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104572) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f85 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 81), (1, 218), (2, 216), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104574) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f86 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 81), (1, 218), (2, 220), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104577) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f87 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 81), (1, 218), (2, 222), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104579) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f88 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 81), (1, 224), (2, 222), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10457b) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 226) (RestInside.out (n := 226) f89 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 227) (ρ' := [(0, 81), (1, 226), (2, 222), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10457d) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 228) (RestInside.out (n := 228) f90 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 229) (ρ' := [(0, 81), (1, 228), (2, 222), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10457f) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f91 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(0, 81), (1, 230), (2, 222), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104585) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f92 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 81), (1, 230), (2, 232), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104587) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f93 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 81), (1, 234), (2, 232), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104589) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f94 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 81), (1, 236), (2, 232), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10458b) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.exec (n := 238) (ρ' := [(0, 81), (1, 236), (2, 232), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104590) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f96 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 81), (1, 239), (2, 232), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104595) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.out (n := 241) f97 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 242) (ρ' := [(0, 81), (1, 239), (2, 241), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104597) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f98 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 81), (1, 239), (2, 243), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10459a) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f99 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 81), (1, 239), (2, 245), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10459c) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_5 code

theorem rest_l10446f_3 [Bindings] (code : CodeMap) :
    Rest (n := 170) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 81), (1, 168), (2, 160), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      773 0x104525 bytes_l10446f_3 b_l10446f_3 := by
  have f60 : InstrSpec 0x104525 [0x31, 0xCA] (fun s => s.RIP = 0x104525) (xorR32R32Effect 0x104525 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104525 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x104525 0xca (by decide)) pre_rip
  have f61 : InstrSpec 0x104527 [0x01, 0xC9] (fun s => s.RIP = 0x104527) (addR32R32Effect 0x104527 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104527 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x104527 0xc9 (by decide)) pre_rip
  have f62 : InstrSpec 0x104529 [0x31, 0xD1] (fun s => s.RIP = 0x104529) (xorR32R32Effect 0x104529 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104529 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x104529 0xd1 (by decide)) pre_rip
  have f63 : InstrSpec 0x10452b [0x66, 0x89, 0x4C, 0x24, 0x1E] (StorePre 0x10452b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x10452b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10452b 5 1 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10452b 5 1 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (mov_m16_r16_effect_step 0x10452b 1 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f64 : InstrSpec 0x104530 [0x0F, 0xB7, 0x4C, 0x24, 0x20] (LoadPre 0x104530 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x104530 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104530 5 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x104530 5 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (movzx_r32_m16_effect_step 0x104530 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f65 : InstrSpec 0x104535 [0x89, 0xCA] (fun s => s.RIP = 0x104535) (movR32R32Effect 0x104535 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x104535 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x104535 0xca (by decide)) pre_rip
  have f66 : InstrSpec 0x104537 [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x104537) (shrR32Effect 0x104537 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x104537 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x104537 0xea 0x2 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x10453a [0x31, 0xCA] (fun s => s.RIP = 0x10453a) (xorR32R32Effect 0x10453a 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10453a 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x10453a 0xca (by decide)) pre_rip
  have f68 : InstrSpec 0x10453c [0x81, 0xE2, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10453c) (andR32Imm32Effect 0x10453c 6 2 0x1320)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10453c 6 2 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x10453c 0xe2 0x1320 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x104542 [0x31, 0xD1] (fun s => s.RIP = 0x104542) (xorR32R32Effect 0x104542 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104542 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x104542 0xd1 (by decide)) pre_rip
  have f70 : InstrSpec 0x104544 [0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x104544) (shlR32Effect 0x104544 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x104544 3 2 2).toInstrSpec (shl_r32_imm8_effect_step 0x104544 0xe2 0x2 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x104547 [0x31, 0xCA] (fun s => s.RIP = 0x104547) (xorR32R32Effect 0x104547 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104547 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x104547 0xca (by decide)) pre_rip
  have f72 : InstrSpec 0x104549 [0x89, 0xD1] (fun s => s.RIP = 0x104549) (movR32R32Effect 0x104549 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x104549 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x104549 0xd1 (by decide)) pre_rip
  have f73 : InstrSpec 0x10454b [0xD1, 0xE9] (fun s => s.RIP = 0x10454b) (shrR32Effect 0x10454b 2 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10454b 2 1 1).toInstrSpec (shr_r32_one_effect_step 0x10454b 0xe9 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x10454d [0x31, 0xD1] (fun s => s.RIP = 0x10454d) (xorR32R32Effect 0x10454d 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10454d 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x10454d 0xd1 (by decide)) pre_rip
  have f75 : InstrSpec 0x10454f [0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10454f) (andR32Imm32Effect 0x10454f 6 1 0x5050)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10454f 6 1 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x10454f 0xe1 0x5050 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x104555 [0x31, 0xCA] (fun s => s.RIP = 0x104555) (xorR32R32Effect 0x104555 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104555 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x104555 0xca (by decide)) pre_rip
  have f77 : InstrSpec 0x104557 [0x01, 0xC9] (fun s => s.RIP = 0x104557) (addR32R32Effect 0x104557 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104557 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x104557 0xc9 (by decide)) pre_rip
  have f78 : InstrSpec 0x104559 [0x31, 0xD1] (fun s => s.RIP = 0x104559) (xorR32R32Effect 0x104559 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104559 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x104559 0xd1 (by decide)) pre_rip
  have f79 : InstrSpec 0x10455b [0x66, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x10455b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10455b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10455b 5 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10455b 5 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m16_r16_effect_step 0x10455b 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f60 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 81), (1, 168), (2, 170), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104527) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f61 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 81), (1, 172), (2, 170), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104529) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f62 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 81), (1, 174), (2, 170), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10452b) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.exec (n := 176) (ρ' := [(0, 81), (1, 174), (2, 170), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104530) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 81), (1, 177), (2, 170), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104535) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f65 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 81), (1, 177), (2, 179), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104537) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f66 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 81), (1, 177), (2, 181), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10453a) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f67 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 81), (1, 177), (2, 183), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10453c) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f68 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 81), (1, 177), (2, 185), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104542) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f69 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 81), (1, 187), (2, 185), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104544) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f70 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 81), (1, 187), (2, 189), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104547) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f71 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 81), (1, 187), (2, 191), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104549) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f72 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 81), (1, 193), (2, 191), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10454b) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f73 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 81), (1, 195), (2, 191), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10454d) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f74 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 81), (1, 197), (2, 191), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10454f) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f75 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 81), (1, 199), (2, 191), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104555) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f76 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 81), (1, 199), (2, 201), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104557) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f77 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 81), (1, 203), (2, 201), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104559) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f78 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 81), (1, 205), (2, 201), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10455b) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.exec (n := 207) (ρ' := [(0, 81), (1, 205), (2, 201), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104560) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l10446f_4 code

theorem rest_l10446f_2 [Bindings] (code : CodeMap) :
    Rest (n := 131) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 81), (1, 125), (2, 129), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      793 0x1044e9 bytes_l10446f_2 b_l10446f_2 := by
  have f40 : InstrSpec 0x1044e9 [0x89, 0xD1] (fun s => s.RIP = 0x1044e9) (movR32R32Effect 0x1044e9 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1044e9 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x1044e9 0xd1 (by decide)) pre_rip
  have f41 : InstrSpec 0x1044eb [0xD1, 0xE9] (fun s => s.RIP = 0x1044eb) (shrR32Effect 0x1044eb 2 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1044eb 2 1 1).toInstrSpec (shr_r32_one_effect_step 0x1044eb 0xe9 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x1044ed [0x31, 0xD1] (fun s => s.RIP = 0x1044ed) (xorR32R32Effect 0x1044ed 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044ed 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1044ed 0xd1 (by decide)) pre_rip
  have f43 : InstrSpec 0x1044ef [0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1044ef) (andR32Imm32Effect 0x1044ef 6 1 0x5050)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1044ef 6 1 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x1044ef 0xe1 0x5050 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1044f5 [0x31, 0xCA] (fun s => s.RIP = 0x1044f5) (xorR32R32Effect 0x1044f5 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044f5 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1044f5 0xca (by decide)) pre_rip
  have f45 : InstrSpec 0x1044f7 [0x01, 0xC9] (fun s => s.RIP = 0x1044f7) (addR32R32Effect 0x1044f7 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1044f7 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x1044f7 0xc9 (by decide)) pre_rip
  have f46 : InstrSpec 0x1044f9 [0x31, 0xD1] (fun s => s.RIP = 0x1044f9) (xorR32R32Effect 0x1044f9 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044f9 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1044f9 0xd1 (by decide)) pre_rip
  have f47 : InstrSpec 0x1044fb [0x66, 0x89, 0x4C, 0x24, 0x1C] (StorePre 0x1044fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1044fb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1044fb 5 1 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1044fb 5 1 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m16_r16_effect_step 0x1044fb 1 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x104500 [0x0F, 0xB7, 0x4C, 0x24, 0x1E] (LoadPre 0x104500 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x104500 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104500 5 1 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x104500 5 1 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (movzx_r32_m16_effect_step 0x104500 1 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f49 : InstrSpec 0x104505 [0x89, 0xCA] (fun s => s.RIP = 0x104505) (movR32R32Effect 0x104505 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x104505 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x104505 0xca (by decide)) pre_rip
  have f50 : InstrSpec 0x104507 [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x104507) (shrR32Effect 0x104507 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x104507 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x104507 0xea 0x2 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x10450a [0x31, 0xCA] (fun s => s.RIP = 0x10450a) (xorR32R32Effect 0x10450a 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10450a 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x10450a 0xca (by decide)) pre_rip
  have f52 : InstrSpec 0x10450c [0x81, 0xE2, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10450c) (andR32Imm32Effect 0x10450c 6 2 0x1320)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10450c 6 2 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x10450c 0xe2 0x1320 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x104512 [0x31, 0xD1] (fun s => s.RIP = 0x104512) (xorR32R32Effect 0x104512 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104512 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x104512 0xd1 (by decide)) pre_rip
  have f54 : InstrSpec 0x104514 [0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x104514) (shlR32Effect 0x104514 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x104514 3 2 2).toInstrSpec (shl_r32_imm8_effect_step 0x104514 0xe2 0x2 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x104517 [0x31, 0xCA] (fun s => s.RIP = 0x104517) (xorR32R32Effect 0x104517 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104517 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x104517 0xca (by decide)) pre_rip
  have f56 : InstrSpec 0x104519 [0x89, 0xD1] (fun s => s.RIP = 0x104519) (movR32R32Effect 0x104519 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x104519 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x104519 0xd1 (by decide)) pre_rip
  have f57 : InstrSpec 0x10451b [0xD1, 0xE9] (fun s => s.RIP = 0x10451b) (shrR32Effect 0x10451b 2 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10451b 2 1 1).toInstrSpec (shr_r32_one_effect_step 0x10451b 0xe9 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x10451d [0x31, 0xD1] (fun s => s.RIP = 0x10451d) (xorR32R32Effect 0x10451d 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10451d 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x10451d 0xd1 (by decide)) pre_rip
  have f59 : InstrSpec 0x10451f [0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10451f) (andR32Imm32Effect 0x10451f 6 1 0x5050)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10451f 6 1 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x10451f 0xe1 0x5050 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f40 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 81), (1, 131), (2, 129), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044eb) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f41 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 81), (1, 133), (2, 129), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044ed) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 81), (1, 135), (2, 129), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044ef) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 81), (1, 137), (2, 129), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044f5) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 81), (1, 137), (2, 139), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044f7) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f45 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 81), (1, 141), (2, 139), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044f9) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 81), (1, 143), (2, 139), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044fb) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(0, 81), (1, 143), (2, 139), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104500) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f48 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 81), (1, 146), (2, 139), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104505) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f49 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 81), (1, 146), (2, 148), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104507) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 81), (1, 146), (2, 150), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10450a) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f51 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 81), (1, 146), (2, 152), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10450c) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 81), (1, 146), (2, 154), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104512) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f53 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 81), (1, 156), (2, 154), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104514) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f54 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 81), (1, 156), (2, 158), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104517) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f55 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 81), (1, 156), (2, 160), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104519) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f56 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 81), (1, 162), (2, 160), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10451b) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f57 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 81), (1, 164), (2, 160), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10451d) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 81), (1, 166), (2, 160), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10451f) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 81), (1, 168), (2, 160), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104525) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_3 code

theorem rest_l10446f_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x10446f bytes_l10446f) [(0, 81), (1, 84), (2, 90), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]
      813 0x1044ac bytes_l10446f_1 b_l10446f_1 := by
  have f20 : InstrSpec 0x1044ac [0x81, 0xE2, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1044ac) (andR32Imm32Effect 0x1044ac 6 2 0x1320)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1044ac 6 2 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1044ac 0xe2 0x1320 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1044b2 [0x31, 0xD1] (fun s => s.RIP = 0x1044b2) (xorR32R32Effect 0x1044b2 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044b2 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1044b2 0xd1 (by decide)) pre_rip
  have f22 : InstrSpec 0x1044b4 [0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x1044b4) (shlR32Effect 0x1044b4 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x1044b4 3 2 2).toInstrSpec (shl_r32_imm8_effect_step 0x1044b4 0xe2 0x2 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1044b7 [0x31, 0xCA] (fun s => s.RIP = 0x1044b7) (xorR32R32Effect 0x1044b7 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044b7 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1044b7 0xca (by decide)) pre_rip
  have f24 : InstrSpec 0x1044b9 [0x89, 0xD1] (fun s => s.RIP = 0x1044b9) (movR32R32Effect 0x1044b9 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1044b9 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x1044b9 0xd1 (by decide)) pre_rip
  have f25 : InstrSpec 0x1044bb [0xD1, 0xE9] (fun s => s.RIP = 0x1044bb) (shrR32Effect 0x1044bb 2 1 1)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x1044bb 2 1 1).toInstrSpec (shr_r32_one_effect_step 0x1044bb 0xe9 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1044bd [0x31, 0xD1] (fun s => s.RIP = 0x1044bd) (xorR32R32Effect 0x1044bd 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044bd 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1044bd 0xd1 (by decide)) pre_rip
  have f27 : InstrSpec 0x1044bf [0x81, 0xE1, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x1044bf) (andR32Imm32Effect 0x1044bf 6 1 0x5050)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1044bf 6 1 0x5050).toInstrSpec (and_r32_imm32_effect_step 0x1044bf 0xe1 0x5050 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x1044c5 [0x31, 0xCA] (fun s => s.RIP = 0x1044c5) (xorR32R32Effect 0x1044c5 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044c5 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1044c5 0xca (by decide)) pre_rip
  have f29 : InstrSpec 0x1044c7 [0x01, 0xC9] (fun s => s.RIP = 0x1044c7) (addR32R32Effect 0x1044c7 2 1 1)
      [.gpr 1, .gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1044c7 2 1 1).toInstrSpec (add_r32_r32_effect_step 0x1044c7 0xc9 (by decide)) pre_rip
  have f30 : InstrSpec 0x1044c9 [0x31, 0xD1] (fun s => s.RIP = 0x1044c9) (xorR32R32Effect 0x1044c9 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044c9 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1044c9 0xd1 (by decide)) pre_rip
  have f31 : InstrSpec 0x1044cb [0x66, 0x89, 0x4C, 0x24, 0x1A] (StorePre 0x1044cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x1044cb + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1044cb 5 1 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1044cb 5 1 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (mov_m16_r16_effect_step 0x1044cb 1 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x1044d0 [0x0F, 0xB7, 0x4C, 0x24, 0x1C] (LoadPre 0x1044d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1044d0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1044d0 5 1 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x1044d0 5 1 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (movzx_r32_m16_effect_step 0x1044d0 1 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x1044d5 [0x89, 0xCA] (fun s => s.RIP = 0x1044d5) (movR32R32Effect 0x1044d5 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1044d5 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x1044d5 0xca (by decide)) pre_rip
  have f34 : InstrSpec 0x1044d7 [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x1044d7) (shrR32Effect 0x1044d7 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x1044d7 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x1044d7 0xea 0x2 (by decide) (by decide)) pre_rip
  have f35 : InstrSpec 0x1044da [0x31, 0xCA] (fun s => s.RIP = 0x1044da) (xorR32R32Effect 0x1044da 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044da 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1044da 0xca (by decide)) pre_rip
  have f36 : InstrSpec 0x1044dc [0x81, 0xE2, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x1044dc) (andR32Imm32Effect 0x1044dc 6 2 0x1320)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1044dc 6 2 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x1044dc 0xe2 0x1320 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x1044e2 [0x31, 0xD1] (fun s => s.RIP = 0x1044e2) (xorR32R32Effect 0x1044e2 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044e2 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1044e2 0xd1 (by decide)) pre_rip
  have f38 : InstrSpec 0x1044e4 [0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x1044e4) (shlR32Effect 0x1044e4 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x1044e4 3 2 2).toInstrSpec (shl_r32_imm8_effect_step 0x1044e4 0xe2 0x2 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x1044e7 [0x31, 0xCA] (fun s => s.RIP = 0x1044e7) (xorR32R32Effect 0x1044e7 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044e7 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1044e7 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 81), (1, 84), (2, 92), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044b2) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 81), (1, 94), (2, 92), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044b4) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 81), (1, 94), (2, 96), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044b7) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 81), (1, 94), (2, 98), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044b9) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 81), (1, 100), (2, 98), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044bb) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 81), (1, 102), (2, 98), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044bd) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 81), (1, 104), (2, 98), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044bf) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 81), (1, 106), (2, 98), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044c5) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f28 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 81), (1, 106), (2, 108), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044c7) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f29 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 81), (1, 110), (2, 108), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044c9) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 81), (1, 112), (2, 108), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044cb) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 81), (1, 112), (2, 108), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044d0) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 81), (1, 115), (2, 108), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044d5) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f33 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 81), (1, 115), (2, 117), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044d7) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 81), (1, 115), (2, 119), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044da) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 81), (1, 115), (2, 121), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044dc) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f36 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 81), (1, 115), (2, 123), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044e2) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f37 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 81), (1, 125), (2, 123), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044e4) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f38 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 81), (1, 125), (2, 127), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044e7) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f39 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 81), (1, 125), (2, 129), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044e9) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_2 code

theorem rest_l10446f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10446f bytes_l10446f) (entryMap (live .l10446f))
      833 0x10446f bytes_l10446f b_l10446f := by
  have f0 : InstrSpec 0x10446f [0x0F, 0xB7, 0x44, 0x24, 0x18] (LoadPre 0x10446f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10446f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10446f 5 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10446f 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m16_effect_step 0x10446f 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104474 [0x89, 0xC1] (fun s => s.RIP = 0x104474) (movR32R32Effect 0x104474 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x104474 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x104474 0xc1 (by decide)) pre_rip
  have f2 : InstrSpec 0x104476 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x104476) (shrR32Effect 0x104476 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x104476 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x104476 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104479 [0x31, 0xC1] (fun s => s.RIP = 0x104479) (xorR32R32Effect 0x104479 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104479 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x104479 0xc1 (by decide)) pre_rip
  have f4 : InstrSpec 0x10447b [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00] (fun s => s.RIP = 0x10447b) (andR32Imm32Effect 0x10447b 6 1 0x1320)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10447b 6 1 0x1320).toInstrSpec (and_r32_imm32_effect_step 0x10447b 0xe1 0x1320 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x104481 [0x31, 0xC8] (fun s => s.RIP = 0x104481) (xorR32R32Effect 0x104481 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104481 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x104481 0xc8 (by decide)) pre_rip
  have f6 : InstrSpec 0x104483 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x104483) (shlR32Effect 0x104483 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x104483 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x104483 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104486 [0x31, 0xC1] (fun s => s.RIP = 0x104486) (xorR32R32Effect 0x104486 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104486 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x104486 0xc1 (by decide)) pre_rip
  have f8 : InstrSpec 0x104488 [0x89, 0xC8] (fun s => s.RIP = 0x104488) (movR32R32Effect 0x104488 2 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x104488 2 0 1).toInstrSpec (mov_r32_r32_effect_step 0x104488 0xc8 (by decide)) pre_rip
  have f9 : InstrSpec 0x10448a [0xD1, 0xE8] (fun s => s.RIP = 0x10448a) (shrR32Effect 0x10448a 2 0 1)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10448a 2 0 1).toInstrSpec (shr_r32_one_effect_step 0x10448a 0xe8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10448c [0x31, 0xC8] (fun s => s.RIP = 0x10448c) (xorR32R32Effect 0x10448c 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10448c 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x10448c 0xc8 (by decide)) pre_rip
  have f11 : InstrSpec 0x10448e [0x25, 0x50, 0x50, 0x00, 0x00] (fun s => s.RIP = 0x10448e) (andEaxImm32Effect 0x10448e 0x5050)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10448e 0x5050).toInstrSpec (and_eax_imm32_effect_step 0x10448e 0x5050) pre_rip
  have f12 : InstrSpec 0x104493 [0x31, 0xC1] (fun s => s.RIP = 0x104493) (xorR32R32Effect 0x104493 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104493 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x104493 0xc1 (by decide)) pre_rip
  have f13 : InstrSpec 0x104495 [0x01, 0xC0] (fun s => s.RIP = 0x104495) (addR32R32Effect 0x104495 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x104495 2 0 0).toInstrSpec (add_r32_r32_effect_step 0x104495 0xc0 (by decide)) pre_rip
  have f14 : InstrSpec 0x104497 [0x31, 0xC8] (fun s => s.RIP = 0x104497) (xorR32R32Effect 0x104497 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104497 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x104497 0xc8 (by decide)) pre_rip
  have f15 : InstrSpec 0x104499 [0x89, 0x84, 0x24, 0xBC, 0x00, 0x00, 0x00] (StorePre 0x104499 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x104499 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x104499 0 (.sib 4 none 0 (.d32 0xbc)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x104499 0 (.sib 4 none 0 (.d32 0xbc))).toInstrSpec (mov_m32_r32_low_effect_step 0x104499 0 (.sib 4 none 0 (.d32 0xbc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1044a0 [0x0F, 0xB7, 0x4C, 0x24, 0x1A] (LoadPre 0x1044a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x1044a0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1044a0 5 1 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x1044a0 5 1 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (movzx_r32_m16_effect_step 0x1044a0 1 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1044a5 [0x89, 0xCA] (fun s => s.RIP = 0x1044a5) (movR32R32Effect 0x1044a5 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1044a5 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x1044a5 0xca (by decide)) pre_rip
  have f18 : InstrSpec 0x1044a7 [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x1044a7) (shrR32Effect 0x1044a7 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x1044a7 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x1044a7 0xea 0x2 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x1044aa [0x31, 0xCA] (fun s => s.RIP = 0x1044aa) (xorR32R32Effect 0x1044aa 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1044aa 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1044aa 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104474) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104476) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104479) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10447b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104481) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 61), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104483) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 65), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104486) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 67), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104488) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 67), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10448a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 67), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10448c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 67), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10448e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 67), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104493) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 75), (1, 77), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104495) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 77), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104497) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 77), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104499) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 81), (1, 77), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044a0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 84), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044a5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 81), (1, 84), (2, 86), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044a7) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 81), (1, 84), (2, 88), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044aa) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 81), (1, 84), (2, 90), (4, 4), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1044ac) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10446f_1 code

theorem block_l10446f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10446f :=
  Rest.liftedBlock (rest_l10446f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10446f x hx)

theorem rest_l1050df [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1050df bytes_l1050df) (entryMap (live .l1050df))
      9 0x1050df bytes_l1050df b_l1050df := by
  have f0 : InstrSpec 0x1050df [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1050df) (movR64R64Effect 0x1050df 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1050df 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1050df 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1050e2 [0x48, 0x81, 0xC4, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1050e2) (addR64Imm32Effect 0x1050e2 4 0xd8)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1050e2 4 0xd8).toInstrSpec (add_r64_imm32_effect_step 0x1050e2 0x48 0xc4 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1050e9 [0x5B] (PopPre 0x1050e9) (popR64Effect 0x1050e9 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1050e9 1 3).toInstrSpec (pop_r64_effect_step 0x1050e9 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1050ea [0x41, 0x5C] (PopPre 0x1050ea) (popR64Effect 0x1050ea 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1050ea 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1050ea 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1050ec [0x41, 0x5D] (PopPre 0x1050ec) (popR64Effect 0x1050ec 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1050ec 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1050ec 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1050ee [0x41, 0x5E] (PopPre 0x1050ee) (popR64Effect 0x1050ee 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1050ee 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1050ee 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1050f0 [0x41, 0x5F] (PopPre 0x1050f0) (popR64Effect 0x1050f0 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1050f0 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1050f0 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1050f2 [0x5D] (PopPre 0x1050f2) (popR64Effect 0x1050f2 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1050f2 1 5).toInstrSpec (pop_r64_effect_step 0x1050f2 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1050f3 [0xC3] (RetPre 0x1050f3) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1050f3).toInstrSpec (ret_effect_step 0x1050f3) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050e2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050e9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050ea) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050ec) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050ee) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050f0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050f2) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1050f3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l1050df [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1050df :=
  Rest.liftedBlock (rest_l1050df code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1050df x hx)

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

theorem_by block_l104370_eval :
    program.runBlock (dialect code) ⟨.l104370, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1043a4_eval :
    program.runBlock (dialect code) ⟨.l1043a4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1043d2_eval :
    program.runBlock (dialect code) ⟨.l1043d2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1043e0_eval :
    program.runBlock (dialect code) ⟨.l1043e0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1043f4_eval :
    program.runBlock (dialect code) ⟨.l1043f4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104413_eval :
    program.runBlock (dialect code) ⟨.l104413, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104424_eval :
    program.runBlock (dialect code) ⟨.l104424, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104434_eval :
    program.runBlock (dialect code) ⟨.l104434, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104446_eval :
    program.runBlock (dialect code) ⟨.l104446, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104468_eval :
    program.runBlock (dialect code) ⟨.l104468, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1050df_eval :
    program.runBlock (dialect code) ⟨.l1050df, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
