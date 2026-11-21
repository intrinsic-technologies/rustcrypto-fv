import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l102980 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102980 bytes_l102980) (entryMap (live .l102980))
      17 0x102980 bytes_l102980 b_l102980 := by
  have f0 : InstrSpec 0x102980 [0x55] (PushPre 0x102980 1) (pushR64Effect 0x102980 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102980 1 5).toInstrSpec (push_r64_effect_step 0x102980 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x102981 [0x41, 0x57] (PushPre 0x102981 2) (pushR64Effect 0x102981 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102981 2 15).toInstrSpec (push_r64_rex_effect_step 0x102981 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x102983 [0x41, 0x56] (PushPre 0x102983 2) (pushR64Effect 0x102983 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102983 2 14).toInstrSpec (push_r64_rex_effect_step 0x102983 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102985 [0x41, 0x55] (PushPre 0x102985 2) (pushR64Effect 0x102985 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102985 2 13).toInstrSpec (push_r64_rex_effect_step 0x102985 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x102987 [0x41, 0x54] (PushPre 0x102987 2) (pushR64Effect 0x102987 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102987 2 12).toInstrSpec (push_r64_rex_effect_step 0x102987 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x102989 [0x53] (PushPre 0x102989 1) (pushR64Effect 0x102989 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x102989 1 3).toInstrSpec (push_r64_effect_step 0x102989 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10298a [0x48, 0x81, 0xEC, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10298a) (subR64Imm32Effect 0x10298a 4 0x98)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x10298a 4 0x98).toInstrSpec (sub_r64_imm32_effect_step 0x10298a 0x48 0xec 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102991 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x102991) (movR64R64Effect 0x102991 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x102991 3 7).toInstrSpec (mov_r64_r64_effect_step 0x102991 0x48 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102994 [0x48, 0xB8, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102994) (movR64Imm64Effect 0x102994 0 0xfffffffe0)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x102994 0 0xfffffffe0).toInstrSpec (mov_r64_imm64_effect_step 0x102994 0x48 0xb8 (by decide) (by decide) 0xfffffffe0) pre_rip
  have f9 : InstrSpec 0x10299e [0x4D, 0x8B, 0x61, 0x10] (LoadPre 0x10299e (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x10299e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10299e 12 (.base 9 (.d8 0x10)))
      [.gpr 9] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x10299e 12 (.base 9 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10299e 0x4d (by decide) 4 (.base 9 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1029a2 [0x49, 0x39, 0xC4] (fun s => s.RIP = 0x1029a2) (cmpR64R64Effect 0x1029a2 12 0)
      [.gpr 12, .gpr 0] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1029a2 12 0).toInstrSpec (cmp_r64_r64_effect_step 0x1029a2 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1029a5 [0x0F, 0x97, 0xC0] (fun s => s.RIP = 0x1029a5) (atFlags (condHolds 7) (setccR8Effect 0x1029a5 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x1029a5 3 0 7).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x1029a5 7 0xc0 (by decide) (by decide) c)) pre_rip
  have f12 : InstrSpec 0x1029a8 [0x4C, 0x89, 0xC7] (fun s => s.RIP = 0x1029a8) (movR64R64Effect 0x1029a8 7 8)
      [.gpr 8] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1029a8 7 8).toInstrSpec (mov_r64_r64_effect_step 0x1029a8 0x4c 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1029ab [0x48, 0xC1, 0xEF, 0x3D] (fun s => s.RIP = 0x1029ab) (shrR64Effect 0x1029ab 4 7 61)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x1029ab 4 7 61).toInstrSpec (shr_r64_imm8_effect_step 0x1029ab 0x48 0xef 0x3d (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1029af [0x40, 0x0F, 0x95, 0xC7] (fun s => s.RIP = 0x1029af) (atFlags (condHolds 5) (setccR8Effect 0x1029af 4 7))
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 7, .rip] :=
    (setccR8Effect_footprint 0x1029af 4 7 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_rex_effect_step 0x1029af 5 0x40 (by decide) 0xc7 (by decide) c)) pre_rip
  have f15 : InstrSpec 0x1029b3 [0x40, 0x08, 0xC7] (fun s => s.RIP = 0x1029b3) (orR8R8Effect 0x1029b3 3 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (orR8R8Effect_footprint 0x1029b3 3 7 0).toInstrSpec (or_r8_r8_rex_effect_step 0x1029b3 0x40 0xc7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102981) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102983) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102985) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102987) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102989) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10298a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102991) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102994) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10299e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029a2) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f10 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 69), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (16, 73), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029a5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (16, 73), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029a8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 78), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (16, 73), (19, 74), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029ab) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.fresh (n := 81) f13 .ZF (fun _ => rfl) (shrR64Effect_fresh 0x1029ab 4 7 61 (by decide) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_
  refine RestInside.exec (n := 82) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 80), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029af) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 83), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029b3) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f15 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 87) (ρ' := [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 85), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029b6) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 88) (jcc_rel8_effect_step 0x1029b6 4 0x8) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102980 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102980 :=
  Rest.liftedBlock (rest_l102980 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102980 x hx)

theorem rest_l1029b8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1029b8 bytes_l1029b8) (entryMap (live .l1029b8))
      2 0x1029b8 bytes_l1029b8 b_l1029b8 := by
  have f0 : InstrSpec 0x1029b8 [0xC6, 0x03, 0x01] (StorePre 0x1029b8 3 (fun s => AddrMode.addr (.base 3 .none) s (0x1029b8 + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x1029b8 (.base 3 .none) 0x1)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1029b8 (.base 3 .none) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x1029b8 (.base 3 .none) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029bb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jmp (n := 54) (jmp_rel32_effect_step 0x1029bb 0x1aa (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1029b8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1029b8 :=
  Rest.liftedBlock (rest_l1029b8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1029b8 x hx)

theorem rest_l1029c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1029c0 bytes_l1029c0) (entryMap (live .l1029c0))
      19 0x1029c0 bytes_l1029c0 b_l1029c0 := by
  have f0 : InstrSpec 0x1029c0 [0x4D, 0x89, 0xCE] (fun s => s.RIP = 0x1029c0) (movR64R64Effect 0x1029c0 14 9)
      [.gpr 9] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1029c0 14 9).toInstrSpec (mov_r64_r64_effect_step 0x1029c0 0x4d 0xce (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1029c3 [0x48, 0x89, 0x5C, 0x24, 0x58] (StorePre 0x1029c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1029c3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1029c3 3 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1029c3 3 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x1029c3 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1029c8 [0x48, 0x89, 0x4C, 0x24, 0x68] (StorePre 0x1029c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1029c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1029c8 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1029c8 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x1029c8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1029cd [0x4C, 0x89, 0x44, 0x24, 0x70] (StorePre 0x1029cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1029cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1029cd 8 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1029cd 8 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x1029cd 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1029d2 [0x44, 0x8B, 0x2A] (LoadPre 0x1029d2 (fun s => AddrMode.addr (.base 2 .none) s (0x1029d2 + BitVec.ofNat 64 3)) 4) (movR32M32Effect 0x1029d2 13 (.base 2 .none))
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x1029d2 13 (.base 2 .none)).toInstrSpec (mov_r32_m32_effect_step 0x1029d2 0x44 (by decide) 5 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1029d5 [0x44, 0x8B, 0x7A, 0x04] (LoadPre 0x1029d5 (fun s => AddrMode.addr (.base 2 (.d8 0x4)) s (0x1029d5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1029d5 15 (.base 2 (.d8 0x4)))
      [.gpr 2] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x1029d5 15 (.base 2 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x1029d5 0x44 (by decide) 7 (.base 2 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1029d9 [0x8B, 0x5A, 0x08] (LoadPre 0x1029d9 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1029d9 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1029d9 3 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x1029d9 3 (.base 2 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x1029d9 3 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1029dc [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1029dc 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1029dc + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1029dc (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1029dc (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1029dc 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1029e8 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1029e8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1029e8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1029e8 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1029e8 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1029e8 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1029f1 [0x48, 0x89, 0x74, 0x24, 0x60] (StorePre 0x1029f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1029f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1029f1 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1029f1 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x1029f1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1029f6 [0x48, 0x8D, 0x6E, 0x20] (fun s => s.RIP = 0x1029f6) (leaR64Effect 0x1029f6 5 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 5, .rip] :=
    (leaR64Effect_footprint 0x1029f6 5 (.base 6 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1029f6 0x48 (by decide) 5 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1029fa [0x44, 0x89, 0x6C, 0x24, 0x10] (StorePre 0x1029fa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1029fa + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1029fa 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1029fa 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_effect_step 0x1029fa 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1029ff [0x44, 0x89, 0x7C, 0x24, 0x14] (StorePre 0x1029ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1029ff + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1029ff 15 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1029ff 15 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_effect_step 0x1029ff 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x102a04 [0x89, 0x5C, 0x24, 0x18] (StorePre 0x102a04 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102a04 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102a04 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102a04 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_low_effect_step 0x102a04 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x102a08 [0xC7, 0x44, 0x24, 0x1C, 0x00, 0x00, 0x00, 0x01] (StorePre 0x102a08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x102a08 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x102a08 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x102a08 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000).toInstrSpec (mov_m32_imm32_effect_step 0x102a08 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide) 0x1000000) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x102a10 [0x48, 0x8D, 0x7C, 0x24, 0x78] (fun s => s.RIP = 0x102a10) (leaR64Effect 0x102a10 7 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102a10 7 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x102a10 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x102a15 [0x48, 0x8D, 0x54, 0x24, 0x10] (fun s => s.RIP = 0x102a15) (leaR64Effect 0x102a15 2 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x102a15 2 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x102a15 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x102a1a [0x48, 0x89, 0xEE] (fun s => s.RIP = 0x102a1a) (movR64R64Effect 0x102a1a 6 5)
      [.gpr 5] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102a1a 6 5).toInstrSpec (mov_r64_r64_effect_step 0x102a1a 0x48 0xee (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x102a1d [0xE8, 0x3E, 0x3F, 0x00, 0x00] (PushPre 0x102a1d 5) (callEffect (fun _ => 0x106960) 0x102a22)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102a1d 0x106960 0x102a22).toInstrSpec (call_rel32_effect_step 0x102a1d 0x3f3e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029c3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029c8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029cd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029d2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029d5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029d9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029dc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029e8) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029f1) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029f6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029fa) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1029ff) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a04) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a08) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a10) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(1, 1), (2, 2), (3, 62), (4, 4), (5, 67), (6, 6), (7, 73), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a15) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(1, 1), (2, 75), (3, 62), (4, 4), (5, 67), (6, 6), (7, 73), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a1a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f17 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(1, 1), (2, 75), (3, 62), (4, 4), (5, 67), (6, 77), (7, 73), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a1d) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(1, 1), (2, 75), (3, 62), (4, 79), (5, 67), (6, 77), (7, 73), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106960) f18 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 81) (by decide) (by decide) rfl rfl

theorem block_l1029c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1029c0 :=
  Rest.liftedBlock (rest_l1029c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1029c0 x hx)

theorem rest_l102a22 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102a22 bytes_l102a22) (entryMap (live .l102a22))
      12 0x102a22 bytes_l102a22 b_l102a22 := by
  have f0 : InstrSpec 0x102a22 [0x48, 0x89, 0x6C, 0x24, 0x30] (StorePre 0x102a22 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x102a22 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a22 5 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a22 5 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x102a22 0x48 (by decide) 5 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102a27 [0x4C, 0x89, 0xE5] (fun s => s.RIP = 0x102a27) (movR64R64Effect 0x102a27 5 12)
      [.gpr 12] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x102a27 5 12).toInstrSpec (mov_r64_r64_effect_step 0x102a27 0x4c 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102a2a [0x48, 0x8D, 0x4C, 0x24, 0x38] (fun s => s.RIP = 0x102a2a) (leaR64Effect 0x102a2a 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x102a2a 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x102a2a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102a2f [0x44, 0x89, 0x6C, 0x24, 0x38] (StorePre 0x102a2f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x102a2f + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x102a2f 13 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x102a2f 13 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m32_r32_effect_step 0x102a2f 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x102a34 [0x44, 0x89, 0x7C, 0x24, 0x3C] (StorePre 0x102a34 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x102a34 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x102a34 15 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x102a34 15 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m32_r32_effect_step 0x102a34 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x102a39 [0x89, 0x5C, 0x24, 0x40] (StorePre 0x102a39 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x102a39 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102a39 3 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x102a39 3 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m32_r32_low_effect_step 0x102a39 3 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x102a3d [0x48, 0xB8, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102a3d) (movR64Imm64Effect 0x102a3d 0 0x100000001)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x102a3d 0 0x100000001).toInstrSpec (mov_r64_imm64_effect_step 0x102a3d 0x48 0xb8 (by decide) (by decide) 0x100000001) pre_rip
  have f7 : InstrSpec 0x102a47 [0x48, 0x89, 0x44, 0x24, 0x44] (StorePre 0x102a47 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x102a47 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a47 0 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a47 0 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_m64_r64_effect_step 0x102a47 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x102a4c [0x4D, 0x8B, 0x3E] (LoadPre 0x102a4c (fun s => AddrMode.addr (.base 14 .none) s (0x102a4c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x102a4c 15 (.base 14 .none))
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x102a4c 15 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x102a4c 0x4d (by decide) 7 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x102a4f [0x4D, 0x8B, 0x6E, 0x08] (LoadPre 0x102a4f (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x102a4f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102a4f 13 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x102a4f 13 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x102a4f 0x4d (by decide) 5 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x102a53 [0x49, 0x83, 0xFC, 0x11] (fun s => s.RIP = 0x102a53) (cmpR64Imm8Effect 0x102a53 12 0x11)
      [.gpr 12] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x102a53 12 0x11).toInstrSpec (cmp_r64_imm8_effect_step 0x102a53 0x49 0xfc 0x11 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a27) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a2a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a2f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a34) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a39) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a3d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a47) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a4c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a4f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 66), (14, 14), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a53) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 66), (14, 14), (15, 64), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a57) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 70) (jcc_rel8_effect_step 0x102a57 2 0x56) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102a22 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102a22 :=
  Rest.liftedBlock (rest_l102a22 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102a22 x hx)

theorem rest_l102a59 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102a59 bytes_l102a59) (entryMap (live .l102a59))
      16 0x102a59 bytes_l102a59 b_l102a59 := by
  have f0 : InstrSpec 0x102a59 [0x48, 0x89, 0xE8] (fun s => s.RIP = 0x102a59) (movR64R64Effect 0x102a59 0 5)
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102a59 0 5).toInstrSpec (mov_r64_r64_effect_step 0x102a59 0x48 0xe8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102a5c [0x48, 0xC1, 0xE8, 0x04] (fun s => s.RIP = 0x102a5c) (shrR64Effect 0x102a5c 4 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x102a5c 4 0 4).toInstrSpec (shr_r64_imm8_effect_step 0x102a5c 0x48 0xe8 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102a60 [0x49, 0xBC, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102a60) (movR64Imm64Effect 0x102a60 12 0xfffffffe0)
      [] [] [.reg 12, .rip] :=
    (movR64Imm64Effect_footprint 0x102a60 12 0xfffffffe0).toInstrSpec (mov_r64_imm64_effect_step 0x102a60 0x49 0xbc (by decide) (by decide) 0xfffffffe0) pre_rip
  have f3 : InstrSpec 0x102a6a [0x49, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x102a6a) (addR64Imm8Effect 0x102a6a 12 0x10)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x102a6a 12 0x10).toInstrSpec (add_r64_imm8_effect_step 0x102a6a 0x49 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102a6e [0x49, 0x21, 0xEC] (fun s => s.RIP = 0x102a6e) (andR64R64Effect 0x102a6e 12 5)
      [.gpr 12, .gpr 5] [] [.reg 12, .flags, .rip] :=
    (andR64R64Effect_footprint 0x102a6e 12 5).toInstrSpec (and_r64_r64_effect_step 0x102a6e 0x49 0xec (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102a71 [0x41, 0x89, 0xEE] (fun s => s.RIP = 0x102a71) (movR32R32Effect 0x102a71 3 14 5)
      [.gpr 5] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x102a71 3 14 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x102a71 0x41 0xee (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102a74 [0x41, 0x83, 0xE6, 0x0F] (fun s => s.RIP = 0x102a74) (andR32Imm8Effect 0x102a74 4 14 0xf)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x102a74 4 14 0xf).toInstrSpec (and_r32_imm8_rex_effect_step 0x102a74 0x41 0xe6 0xf (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102a78 [0x4B, 0x8D, 0x1C, 0x27] (fun s => s.RIP = 0x102a78) (leaR64Effect 0x102a78 3 (.sib 15 (some 12) 0 .none))
      [.gpr 15, .gpr 12] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x102a78 3 (.sib 15 (some 12) 0 .none)).toInstrSpec (lea_r64_effect_step 0x102a78 0x4b (by decide) 3 (.sib 15 (some 12) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102a7c [0x4D, 0x01, 0xEC] (fun s => s.RIP = 0x102a7c) (addR64R64Effect 0x102a7c 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (addR64R64Effect_footprint 0x102a7c 12 13).toInstrSpec (add_r64_r64_effect_step 0x102a7c 0x4d 0xec (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x102a7f [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x102a7f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102a7f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a7f 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a7f 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x102a7f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x102a84 [0x4C, 0x89, 0x7C, 0x24, 0x18] (StorePre 0x102a84 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102a84 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a84 15 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a84 15 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x102a84 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x102a89 [0x4C, 0x89, 0x6C, 0x24, 0x20] (StorePre 0x102a89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102a89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a89 13 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a89 13 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x102a89 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x102a8e [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x102a8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102a8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a8e 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102a8e 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x102a8e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x102a93 [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x102a93) (leaR64Effect 0x102a93 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102a93 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x102a93 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x102a98 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x102a98) (leaR64Effect 0x102a98 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102a98 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x102a98 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x102a9d [0xE8, 0x3E, 0x5A, 0x00, 0x00] (PushPre 0x102a9d 5) (callEffect (fun _ => 0x1084e0) 0x102aa2)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102a9d 0x1084e0 0x102aa2).toInstrSpec (call_rel32_effect_step 0x102a9d 0x5a3e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (4, 4), (5, 5), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a5c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a60) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (12, 57), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a6a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (12, 59), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a6e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (12, 61), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a71) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (12, 61), (13, 13), (14, 63), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a74) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 1), (4, 4), (5, 5), (11, 11), (12, 61), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a78) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 61), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a7c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a7f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a84) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a89) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a8e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a93) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (7, 75), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a98) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 4), (5, 5), (6, 77), (7, 75), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102a9d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 55), (1, 1), (3, 67), (4, 79), (5, 5), (6, 77), (7, 75), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e0) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 81) (by decide) (by decide) rfl rfl

theorem block_l102a59 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102a59 :=
  Rest.liftedBlock (rest_l102a59 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102a59 x hx)

theorem rest_l102aa2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102aa2 bytes_l102aa2) (entryMap (live .l102aa2))
      3 0x102aa2 bytes_l102aa2 b_l102aa2 := by
  have f0 : InstrSpec 0x102aa2 [0x49, 0x89, 0xDF] (fun s => s.RIP = 0x102aa2) (movR64R64Effect 0x102aa2 15 3)
      [.gpr 3] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x102aa2 15 3).toInstrSpec (mov_r64_r64_effect_step 0x102aa2 0x49 0xdf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102aa5 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x102aa5) (testR64R64Effect 0x102aa5 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x102aa5 14 14).toInstrSpec (test_r64_r64_effect_step 0x102aa5 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102aa5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102aa8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x102aa8 5 0x14) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102aa2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102aa2 :=
  Rest.liftedBlock (rest_l102aa2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102aa2 x hx)

theorem rest_l102aaa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102aaa bytes_l102aaa) (entryMap (live .l102aaa))
      1 0x102aaa bytes_l102aaa b_l102aaa := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x102aaa 0x8f (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l102aaa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102aaa :=
  Rest.liftedBlock (rest_l102aaa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102aaa x hx)

theorem rest_l102aaf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102aaf bytes_l102aaf) (entryMap (live .l102aaf))
      4 0x102aaf bytes_l102aaf b_l102aaf := by
  have f0 : InstrSpec 0x102aaf [0x4D, 0x89, 0xEC] (fun s => s.RIP = 0x102aaf) (movR64R64Effect 0x102aaf 12 13)
      [.gpr 13] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x102aaf 12 13).toInstrSpec (mov_r64_r64_effect_step 0x102aaf 0x4d 0xec (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102ab2 [0x49, 0x89, 0xEE] (fun s => s.RIP = 0x102ab2) (movR64R64Effect 0x102ab2 14 5)
      [.gpr 5] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x102ab2 14 5).toInstrSpec (mov_r64_r64_effect_step 0x102ab2 0x49 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102ab5 [0x4D, 0x85, 0xF6] (fun s => s.RIP = 0x102ab5) (testR64R64Effect 0x102ab5 14 14)
      [.gpr 14, .gpr 14] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x102ab5 14 14).toInstrSpec (test_r64_r64_effect_step 0x102ab5 0x4d 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ab2) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ab5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ab8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x102ab8 4 0x80) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l102aaf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102aaf :=
  Rest.liftedBlock (rest_l102aaf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102aaf x hx)

theorem rest_l102abe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102abe bytes_l102abe) (entryMap (live .l102abe))
      9 0x102abe bytes_l102abe b_l102abe := by
  have f0 : InstrSpec 0x102abe [0xB8, 0x10, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102abe) (movR32Imm32Effect 0x102abe 5 0 0x10)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x102abe 5 0 0x10).toInstrSpec (mov_r32_imm32_effect_step 0x102abe 0xb8 (by decide) 0x10) pre_rip
  have f1 : InstrSpec 0x102ac3 [0x4C, 0x29, 0xF0] (fun s => s.RIP = 0x102ac3) (subR64R64Effect 0x102ac3 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x102ac3 0 14).toInstrSpec (sub_r64_r64_effect_step 0x102ac3 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102ac6 [0x31, 0xD2] (fun s => s.RIP = 0x102ac6) (xorR32R32Effect 0x102ac6 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102ac6 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x102ac6 0xd2 (by decide)) pre_rip
  have f3 : InstrSpec 0x102ac8 [0x49, 0x83, 0xFE, 0x10] (fun s => s.RIP = 0x102ac8) (cmpR64Imm8Effect 0x102ac8 14 0x10)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x102ac8 14 0x10).toInstrSpec (cmp_r64_imm8_effect_step 0x102ac8 0x49 0xfe 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102acc [0x48, 0x0F, 0x42, 0xD0] (fun s => s.RIP = 0x102acc) (atFlags (condHolds 2) (cmovR64R64Effect 0x102acc 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x102acc 4 2 0 2).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x102acc 2 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f5 : InstrSpec 0x102ad0 [0x4A, 0x8D, 0x3C, 0x34] (fun s => s.RIP = 0x102ad0) (leaR64Effect 0x102ad0 7 (.sib 4 (some 14) 0 .none))
      [.gpr 4, .gpr 14] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102ad0 7 (.sib 4 (some 14) 0 .none)).toInstrSpec (lea_r64_effect_step 0x102ad0 0x4a (by decide) 7 (.sib 4 (some 14) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102ad4 [0x48, 0x81, 0xC7, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102ad4) (addR64Imm32Effect 0x102ad4 7 0x88)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x102ad4 7 0x88).toInstrSpec (add_r64_imm32_effect_step 0x102ad4 0x48 0xc7 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102adb [0x31, 0xF6] (fun s => s.RIP = 0x102adb) (xorR32R32Effect 0x102adb 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x102adb 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x102adb 0xf6 (by decide)) pre_rip
  have f8 : InstrSpec 0x102add [0xFF, 0x15, 0x45, 0xE7, 0x0F, 0x00] (GoesTo (CallMemPre 0x102add (.rip 0xfe745)) (callEffect (callMemPtr 0x102add (.rip 0xfe745)) (0x102add + BitVec.ofNat 64 (callMemLen (.rip 0xfe745)))) 0x103eb0) (callEffect (callMemPtr 0x102add (.rip 0xfe745)) (0x102add + BitVec.ofNat 64 (callMemLen (.rip 0xfe745))))
      [.gpr 4] [] [.reg 4, .rip] :=
    ((callMemEffect_footprint 0x102add (.rip 0xfe745)).toInstrSpec (call_m64_effect_step 0x102add (.rip 0xfe745) (by decide) (by decide) (by decide)) (CallMemPre.of_addr rfl (by lift_reads))).goesTo 0x103eb0
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ac3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ac6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ac8) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102acc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ad0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 63), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ad4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 6), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102adb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 4), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102add) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103eb0) f8 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 71) (by decide) (by decide) rfl rfl

theorem block_l102abe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102abe :=
  Rest.liftedBlock (rest_l102abe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102abe x hx)

theorem rest_l102ae3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102ae3 bytes_l102ae3) (entryMap (live .l102ae3))
      7 0x102ae3 bytes_l102ae3 b_l102ae3 := by
  have f0 : InstrSpec 0x102ae3 [0x4C, 0x89, 0x6C, 0x24, 0x50] (StorePre 0x102ae3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102ae3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102ae3 13 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102ae3 13 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x102ae3 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x102ae8 [0x4C, 0x8D, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102ae8) (leaR64Effect 0x102ae8 13 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x102ae8 13 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x102ae8 0x4c (by decide) 5 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102af0 [0x48, 0x8D, 0x1D, 0x09, 0x14, 0x00, 0x00] (fun s => s.RIP = 0x102af0) (leaR64Effect 0x102af0 3 (.rip 0x1409))
      [] [] [.reg 3, .rip] :=
    (leaR64Effect_footprint 0x102af0 3 (.rip 0x1409)).toInstrSpec (lea_r64_effect_step 0x102af0 0x48 (by decide) 3 (.rip 0x1409) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x102af7 [0x4C, 0x89, 0xEF] (fun s => s.RIP = 0x102af7) (movR64R64Effect 0x102af7 7 13)
      [.gpr 13] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102af7 7 13).toInstrSpec (mov_r64_r64_effect_step 0x102af7 0x4c 0xef (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102afa [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x102afa) (movR64R64Effect 0x102afa 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102afa 6 15).toInstrSpec (mov_r64_r64_effect_step 0x102afa 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x102afd [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x102afd) (movR64R64Effect 0x102afd 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x102afd 2 14).toInstrSpec (mov_r64_r64_effect_step 0x102afd 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102b00 [0xFF, 0xD3] (GoesTo (CallPre 0x102b00 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x102b02) 0x103f00) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x102b02)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x102b00 3 0x102b02).toInstrSpec (call_r64_effect_step 0x102b00 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102ae8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102af0) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 56), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102af7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 56), (4, 4), (5, 5), (7, 58), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102afa) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 56), (4, 4), (5, 5), (6, 60), (7, 58), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102afd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(2, 62), (3, 56), (4, 4), (5, 5), (6, 60), (7, 58), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b00) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(2, 62), (3, 56), (4, 64), (5, 5), (6, 60), (7, 58), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f6 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l102ae3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102ae3 :=
  Rest.liftedBlock (rest_l102ae3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102ae3 x hx)

theorem rest_l102b02 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102b02 bytes_l102b02) (entryMap (live .l102b02))
      8 0x102b02 bytes_l102b02 b_l102b02 := by
  have f0 : InstrSpec 0x102b02 [0x48, 0x8D, 0x44, 0x24, 0x38] (fun s => s.RIP = 0x102b02) (leaR64Effect 0x102b02 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x102b02 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (lea_r64_effect_step 0x102b02 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102b07 [0x48, 0x89, 0x44, 0x24, 0x10] (StorePre 0x102b07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102b07 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b07 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102b07 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x102b07 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x102b0c [0x4C, 0x89, 0x6C, 0x24, 0x18] (StorePre 0x102b0c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102b0c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b0c 13 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102b0c 13 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x102b0c 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x102b11 [0x4C, 0x89, 0x6C, 0x24, 0x20] (StorePre 0x102b11 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102b11 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b11 13 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102b11 13 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x102b11 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x102b16 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00] (StorePre 0x102b16 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102b16 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102b16 (.sib 4 none 0 (.d8 0x28)) 0x1)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x102b16 (.sib 4 none 0 (.d8 0x28)) 0x1).toInstrSpec (mov_m64_imm32_effect_step 0x102b16 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x102b1f [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x102b1f) (leaR64Effect 0x102b1f 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102b1f 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x102b1f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x102b24 [0x48, 0x8D, 0x74, 0x24, 0x10] (fun s => s.RIP = 0x102b24) (leaR64Effect 0x102b24 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x102b24 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (lea_r64_effect_step 0x102b24 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x102b29 [0xE8, 0xB2, 0x59, 0x00, 0x00] (PushPre 0x102b29 5) (callEffect (fun _ => 0x1084e0) 0x102b2e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102b29 0x1084e0 0x102b2e).toInstrSpec (call_rel32_effect_step 0x102b29 0x59b2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b07) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b0c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b11) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b16) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b1f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (7, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b24) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (6, 61), (7, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b29) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (3, 3), (4, 63), (5, 5), (6, 61), (7, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1084e0) f7 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 65) (by decide) (by decide) rfl rfl

theorem block_l102b02 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102b02 :=
  Rest.liftedBlock (rest_l102b02 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102b02 x hx)

theorem rest_l102b2e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102b2e bytes_l102b2e) (entryMap (live .l102b2e))
      5 0x102b2e bytes_l102b2e b_l102b2e := by
  have f0 : InstrSpec 0x102b2e [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x102b2e) (movR64R64Effect 0x102b2e 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x102b2e 7 12).toInstrSpec (mov_r64_r64_effect_step 0x102b2e 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102b31 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x102b31) (movR64R64Effect 0x102b31 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x102b31 6 13).toInstrSpec (mov_r64_r64_effect_step 0x102b31 0x4c 0xee (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102b34 [0x4C, 0x8B, 0x6C, 0x24, 0x50] (LoadPre 0x102b34 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102b34 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102b34 13 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x102b34 13 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x102b34 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x102b39 [0x4C, 0x89, 0xF2] (fun s => s.RIP = 0x102b39) (movR64R64Effect 0x102b39 2 14)
      [.gpr 14] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x102b39 2 14).toInstrSpec (mov_r64_r64_effect_step 0x102b39 0x4c 0xf2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102b3c [0xFF, 0xD3] (GoesTo (CallPre 0x102b3c 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x102b3e) 0x103f00) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x102b3e)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    ((callRegEffect_footprint 0x102b3c 3 0x102b3e).toInstrSpec (call_r64_effect_step 0x102b3c 0xd3 (by decide) (by decide)) (CallPre.of_stateOf (target := fun s => (Operand.reg 3 : Operand 64).read s) (by lift_reads) (by lift_reads))).goesTo 0x103f00
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b34) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b39) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 59), (3, 3), (4, 4), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b3c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 59), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f00) f4 (fun _ h => h.2) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l102b2e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102b2e :=
  Rest.liftedBlock (rest_l102b2e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102b2e x hx)

theorem rest_l102b3e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102b3e bytes_l102b3e) (entryMap (live .l102b3e))
      9 0x102b3e bytes_l102b3e b_l102b3e := by
  have f0 : InstrSpec 0x102b3e [0x48, 0x8B, 0x5C, 0x24, 0x58] (LoadPre 0x102b3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x102b3e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102b3e 3 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x102b3e 3 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x102b3e 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x102b43 [0x48, 0x8D, 0x7B, 0x01] (fun s => s.RIP = 0x102b43) (leaR64Effect 0x102b43 7 (.base 3 (.d8 0x1)))
      [.gpr 3] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x102b43 7 (.base 3 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x102b43 0x48 (by decide) 7 (.base 3 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102b47 [0x48, 0x89, 0x2C, 0x24] (StorePre 0x102b47 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102b47 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102b47 5 (.sib 4 none 0 .none))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x102b47 5 (.sib 4 none 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x102b47 0x48 (by decide) 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x102b4b [0x48, 0x8D, 0x54, 0x24, 0x78] (fun s => s.RIP = 0x102b4b) (leaR64Effect 0x102b4b 2 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x102b4b 2 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (lea_r64_effect_step 0x102b4b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x102b50 [0x48, 0x8B, 0x74, 0x24, 0x60] (LoadPre 0x102b50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x102b50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102b50 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x102b50 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x102b50 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x102b55 [0x48, 0x8B, 0x4C, 0x24, 0x68] (LoadPre 0x102b55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x102b55 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102b55 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x102b55 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x102b55 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x102b5a [0x4C, 0x8B, 0x44, 0x24, 0x70] (LoadPre 0x102b5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x102b5a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102b5a 8 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x102b5a 8 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x102b5a 0x4c (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x102b5f [0x4D, 0x89, 0xE9] (fun s => s.RIP = 0x102b5f) (movR64R64Effect 0x102b5f 9 13)
      [.gpr 13] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x102b5f 9 13).toInstrSpec (mov_r64_r64_effect_step 0x102b5f 0x4d 0xe9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x102b62 [0xE8, 0xB9, 0xF0, 0xFF, 0xFF] (PushPre 0x102b62 5) (callEffect (fun _ => 0x101c20) 0x102b67)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x102b62 0x101c20 0x102b67).toInstrSpec (call_rel32_effect_step 0x102b62 0xfffff0b9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 53), (4, 4), (5, 5), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b43) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b47) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 53), (4, 4), (5, 5), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b4b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(2, 58), (3, 53), (4, 4), (5, 5), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b50) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(2, 58), (3, 53), (4, 4), (5, 5), (6, 60), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b55) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(1, 62), (2, 58), (3, 53), (4, 4), (5, 5), (6, 60), (7, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b5a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 62), (2, 58), (3, 53), (4, 4), (5, 5), (6, 60), (7, 55), (8, 64), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b5f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 62), (2, 58), (3, 53), (4, 4), (5, 5), (6, 60), (7, 55), (8, 64), (9, 66), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b62) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(1, 62), (2, 58), (3, 53), (4, 68), (5, 5), (6, 60), (7, 55), (8, 64), (9, 66), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101c20) f8 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 70) (by decide) (by decide) rfl rfl

theorem block_l102b3e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102b3e :=
  Rest.liftedBlock (rest_l102b3e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102b3e x hx)

theorem rest_l102b67 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102b67 bytes_l102b67) (entryMap (live .l102b67))
      1 0x102b67 bytes_l102b67 b_l102b67 := by
  have f0 : InstrSpec 0x102b67 [0xC6, 0x03, 0x00] (StorePre 0x102b67 3 (fun s => AddrMode.addr (.base 3 .none) s (0x102b67 + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x102b67 (.base 3 .none) 0x0)
      [.gpr 3] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x102b67 (.base 3 .none) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x102b67 (.base 3 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b6a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l102b67 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102b67 :=
  Rest.liftedBlock (rest_l102b67 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102b67 x hx)

theorem rest_l102b6a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x102b6a bytes_l102b6a) (entryMap (live .l102b6a))
      9 0x102b6a bytes_l102b6a b_l102b6a := by
  have f0 : InstrSpec 0x102b6a [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x102b6a) (movR64R64Effect 0x102b6a 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x102b6a 0 3).toInstrSpec (mov_r64_r64_effect_step 0x102b6a 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x102b6d [0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x102b6d) (addR64Imm32Effect 0x102b6d 4 0x98)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x102b6d 4 0x98).toInstrSpec (add_r64_imm32_effect_step 0x102b6d 0x48 0xc4 0x98 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x102b74 [0x5B] (PopPre 0x102b74) (popR64Effect 0x102b74 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102b74 1 3).toInstrSpec (pop_r64_effect_step 0x102b74 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x102b75 [0x41, 0x5C] (PopPre 0x102b75) (popR64Effect 0x102b75 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102b75 2 12).toInstrSpec (pop_r64_rex_effect_step 0x102b75 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x102b77 [0x41, 0x5D] (PopPre 0x102b77) (popR64Effect 0x102b77 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102b77 2 13).toInstrSpec (pop_r64_rex_effect_step 0x102b77 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x102b79 [0x41, 0x5E] (PopPre 0x102b79) (popR64Effect 0x102b79 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102b79 2 14).toInstrSpec (pop_r64_rex_effect_step 0x102b79 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x102b7b [0x41, 0x5F] (PopPre 0x102b7b) (popR64Effect 0x102b7b 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102b7b 2 15).toInstrSpec (pop_r64_rex_effect_step 0x102b7b 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x102b7d [0x5D] (PopPre 0x102b7d) (popR64Effect 0x102b7d 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x102b7d 1 5).toInstrSpec (pop_r64_effect_step 0x102b7d 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x102b7e [0xC3] (RetPre 0x102b7e) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x102b7e).toInstrSpec (ret_effect_step 0x102b7e) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b6d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b74) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b75) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b77) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b79) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b7b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b7d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x102b7e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l102b6a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l102b6a :=
  Rest.liftedBlock (rest_l102b6a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l102b6a x hx)

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

theorem_by block_l102980_eval :
    program.runBlock (dialect code) ⟨.l102980, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1029b8_eval :
    program.runBlock (dialect code) ⟨.l1029b8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1029c0_eval :
    program.runBlock (dialect code) ⟨.l1029c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102a22_eval :
    program.runBlock (dialect code) ⟨.l102a22, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102a59_eval :
    program.runBlock (dialect code) ⟨.l102a59, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102aa2_eval :
    program.runBlock (dialect code) ⟨.l102aa2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102aaa_eval :
    program.runBlock (dialect code) ⟨.l102aaa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102aaf_eval :
    program.runBlock (dialect code) ⟨.l102aaf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102abe_eval :
    program.runBlock (dialect code) ⟨.l102abe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102ae3_eval :
    program.runBlock (dialect code) ⟨.l102ae3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102b02_eval :
    program.runBlock (dialect code) ⟨.l102b02, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102b2e_eval :
    program.runBlock (dialect code) ⟨.l102b2e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102b3e_eval :
    program.runBlock (dialect code) ⟨.l102b3e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102b67_eval :
    program.runBlock (dialect code) ⟨.l102b67, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l102b6a_eval :
    program.runBlock (dialect code) ⟨.l102b6a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
