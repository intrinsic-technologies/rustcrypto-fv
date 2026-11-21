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

theorem rest_l128910 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128910 bytes_l128910) (entryMap (live .l128910))
      13 0x128910 bytes_l128910 b_l128910 := by
  have f0 : InstrSpec 0x128910 [0x55] (PushPre 0x128910 1) (pushR64Effect 0x128910 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128910 1 5).toInstrSpec (push_r64_effect_step 0x128910 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x128911 [0x48, 0x89, 0xE5] (fun s => s.RIP = 0x128911) (movR64R64Effect 0x128911 5 4)
      [.gpr 4] [] [.reg 5, .rip] :=
    (movR64R64Effect_footprint 0x128911 5 4).toInstrSpec (mov_r64_r64_effect_step 0x128911 0x48 0xe5 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128914 [0x41, 0x57] (PushPre 0x128914 2) (pushR64Effect 0x128914 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128914 2 15).toInstrSpec (push_r64_rex_effect_step 0x128914 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x128916 [0x41, 0x56] (PushPre 0x128916 2) (pushR64Effect 0x128916 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128916 2 14).toInstrSpec (push_r64_rex_effect_step 0x128916 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x128918 [0x41, 0x55] (PushPre 0x128918 2) (pushR64Effect 0x128918 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x128918 2 13).toInstrSpec (push_r64_rex_effect_step 0x128918 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x12891a [0x41, 0x54] (PushPre 0x12891a 2) (pushR64Effect 0x12891a 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12891a 2 12).toInstrSpec (push_r64_rex_effect_step 0x12891a 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x12891c [0x53] (PushPre 0x12891c 1) (pushR64Effect 0x12891c 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x12891c 1 3).toInstrSpec (push_r64_effect_step 0x12891c 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x12891d [0x48, 0x83, 0xEC, 0x38] (fun s => s.RIP = 0x12891d) (subR64Imm8Effect 0x12891d 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x12891d 4 0x38).toInstrSpec (sub_r64_imm8_effect_step 0x12891d 0x48 0xec 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x128921 [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x128921) (movR64R64Effect 0x128921 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x128921 3 7).toInstrSpec (mov_r64_r64_effect_step 0x128921 0x48 0xfb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x128924 [0x4C, 0x8B, 0x3F] (LoadPre 0x128924 (fun s => AddrMode.addr (.base 7 .none) s (0x128924 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128924 15 (.base 7 .none))
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x128924 15 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128924 0x4c (by decide) 7 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x128927 [0xB0, 0x01] (fun s => s.RIP = 0x128927) (movR8Imm8Effect 0x128927 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x128927 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128927 0xb0 (by decide) 0x1) pre_rip
  have f11 : InstrSpec 0x128929 [0x80, 0x7F, 0x10, 0x00] (LoadPre 0x128929 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x128929 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x128929 4 (.base 7 (.d8 0x10)) 0x0)
      [.gpr 7] [] [.flags, .rip] :=
    (cmpM8Imm8Effect_footprint 0x128929 4 (.base 7 (.d8 0x10)) 0x0).toInstrSpec (cmp_m8_imm8_effect_step 0x128929 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128911) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128914) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128916) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128918) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12891a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12891c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12891d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128921) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128924) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128927) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 71), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128929) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 73), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 71), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12892d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel8_effect_step 0x12892d 4 0x1b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128910 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128910 :=
  Rest.liftedBlock (rest_l128910 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128910 x hx)

theorem rest_l12892f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12892f bytes_l12892f) (entryMap (live .l12892f))
      12 0x12892f bytes_l12892f b_l12892f := by
  have f0 : InstrSpec 0x12892f [0x88, 0x43, 0x10] (StorePre 0x12892f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12892f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12892f 3 0 (.base 3 (.d8 0x10)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x12892f 3 0 (.base 3 (.d8 0x10))).toInstrSpec (mov_m8_r8_effect_step 0x12892f 0 (by decide) (.base 3 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x128932 [0x49, 0xFF, 0xC7] (fun s => s.RIP = 0x128932) (incR64Effect 0x128932 15)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (incR64Effect_footprint 0x128932 15).toInstrSpec (inc_r64_effect_step 0x128932 0x49 0xc7 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x128935 [0x4C, 0x89, 0x3B] (StorePre 0x128935 3 (fun s => AddrMode.addr (.base 3 .none) s (0x128935 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x128935 15 (.base 3 .none))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM64R64Effect_footprint 0x128935 15 (.base 3 .none)).toInstrSpec (mov_m64_r64_effect_step 0x128935 0x4c (by decide) 7 (.base 3 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x128938 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x128938) (movR64R64Effect 0x128938 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x128938 0 3).toInstrSpec (mov_r64_r64_effect_step 0x128938 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12893b [0x48, 0x83, 0xC4, 0x38] (fun s => s.RIP = 0x12893b) (addR64Imm8Effect 0x12893b 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x12893b 4 0x38).toInstrSpec (add_r64_imm8_effect_step 0x12893b 0x48 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x12893f [0x5B] (PopPre 0x12893f) (popR64Effect 0x12893f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x12893f 1 3).toInstrSpec (pop_r64_effect_step 0x12893f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x128940 [0x41, 0x5C] (PopPre 0x128940) (popR64Effect 0x128940 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128940 2 12).toInstrSpec (pop_r64_rex_effect_step 0x128940 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x128942 [0x41, 0x5D] (PopPre 0x128942) (popR64Effect 0x128942 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128942 2 13).toInstrSpec (pop_r64_rex_effect_step 0x128942 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x128944 [0x41, 0x5E] (PopPre 0x128944) (popR64Effect 0x128944 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128944 2 14).toInstrSpec (pop_r64_rex_effect_step 0x128944 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f9 : InstrSpec 0x128946 [0x41, 0x5F] (PopPre 0x128946) (popR64Effect 0x128946 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128946 2 15).toInstrSpec (pop_r64_rex_effect_step 0x128946 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x128948 [0x5D] (PopPre 0x128948) (popR64Effect 0x128948 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x128948 1 5).toInstrSpec (pop_r64_effect_step 0x128948 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x128949 [0xC3] (RetPre 0x128949) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x128949).toInstrSpec (ret_effect_step 0x128949) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128932) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128935) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128938) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12893b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12893f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128940) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128942) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128944) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128946) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 75) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 74), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128948) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 77), (5, 76), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128949) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f11 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 81) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 61), (4, 80), (5, 76), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) f11 (by decide) rfl rfl rfl (by decide)

theorem block_l12892f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12892f :=
  Rest.liftedBlock (rest_l12892f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12892f x hx)

theorem rest_l12894a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12894a bytes_l12894a) (entryMap (live .l12894a))
      3 0x12894a bytes_l12894a b_l12894a := by
  have f0 : InstrSpec 0x12894a [0x4C, 0x8B, 0x73, 0x08] (LoadPre 0x12894a (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12894a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12894a 14 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x12894a 14 (.base 3 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12894a 0x4c (by decide) 6 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12894e [0x41, 0xF6, 0x46, 0x12, 0x80] (LoadPre 0x12894e (fun s => AddrMode.addr (.base 14 (.d8 0x12)) s (0x12894e + BitVec.ofNat 64 5)) 1) (testM8Imm8Effect 0x12894e 5 (.base 14 (.d8 0x12)) 0x80)
      [.gpr 14] [] [.flags, .rip] :=
    (testM8Imm8Effect_footprint 0x12894e 5 (.base 14 (.d8 0x12)) 0x80).toInstrSpec (test_m8_imm8_rex_effect_step 0x12894e 0x41 (by decide) (.base 14 (.d8 0x12)) (by decide) (by decide) (by decide) 0x80) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (14, 53), (15, 15)]) (p' := 0x12894e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (14, 53), (15, 15), (19, 55)]) (p' := 0x128953) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x128953 5 0x48) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12894a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12894a :=
  Rest.liftedBlock (rest_l12894a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12894a x hx)

theorem rest_l128955 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128955 bytes_l128955) (entryMap (live .l128955))
      13 0x128955 bytes_l128955 b_l128955 := by
  have f0 : InstrSpec 0x128955 [0x31, 0xC0] (fun s => s.RIP = 0x128955) (xorR32R32Effect 0x128955 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x128955 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x128955 0xc0 (by decide)) pre_rip
  have f1 : InstrSpec 0x128957 [0x4D, 0x85, 0xFF] (fun s => s.RIP = 0x128957) (testR64R64Effect 0x128957 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x128957 15 15).toInstrSpec (test_r64_r64_effect_step 0x128957 0x4d 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12895a [0x48, 0x8D, 0x3D, 0xCF, 0xB2, 0x0D, 0x00] (fun s => s.RIP = 0x12895a) (leaR64Effect 0x12895a 7 (.rip 0xdb2cf))
      [] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x12895a 7 (.rip 0xdb2cf)).toInstrSpec (lea_r64_effect_step 0x12895a 0x48 (by decide) 7 (.rip 0xdb2cf) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128961 [0x48, 0x8D, 0x0D, 0xBF, 0xB2, 0x0D, 0x00] (fun s => s.RIP = 0x128961) (leaR64Effect 0x128961 1 (.rip 0xdb2bf))
      [] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x128961 1 (.rip 0xdb2bf)).toInstrSpec (lea_r64_effect_step 0x128961 0x48 (by decide) 1 (.rip 0xdb2bf) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x128968 [0x48, 0x0F, 0x44, 0xCF] (fun s => s.RIP = 0x128968) (atFlags (condHolds 4) (cmovR64R64Effect 0x128968 4 1 7))
      [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 1, .rip] :=
    (cmovR64R64Effect_footprint 0x128968 4 1 7 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x128968 4 0x48 (by decide) 0xcf (by decide) c)) pre_rip
  have f5 : InstrSpec 0x12896c [0x0F, 0x95, 0xC0] (fun s => s.RIP = 0x12896c) (atFlags (condHolds 5) (setccR8Effect 0x12896c 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x12896c 3 0 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x12896c 5 0xc0 (by decide) (by decide) c)) pre_rip
  have f6 : InstrSpec 0x12896f [0x48, 0xFF, 0xC0] (fun s => s.RIP = 0x12896f) (incR64Effect 0x12896f 0)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (incR64Effect_footprint 0x12896f 0).toInstrSpec (inc_r64_effect_step 0x12896f 0x48 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x128972 [0x49, 0x8B, 0x3E] (LoadPre 0x128972 (fun s => AddrMode.addr (.base 14 .none) s (0x128972 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128972 7 (.base 14 .none))
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128972 7 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x128972 0x49 (by decide) 7 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x128975 [0x4D, 0x8B, 0x46, 0x08] (LoadPre 0x128975 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x128975 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128975 8 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x128975 8 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x128975 0x4d (by decide) 0 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x128979 [0x49, 0x89, 0xF4] (fun s => s.RIP = 0x128979) (movR64R64Effect 0x128979 12 6)
      [.gpr 6] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x128979 12 6).toInstrSpec (mov_r64_r64_effect_step 0x128979 0x49 0xf4 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x12897c [0x48, 0x89, 0xCE] (fun s => s.RIP = 0x12897c) (movR64R64Effect 0x12897c 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x12897c 6 1).toInstrSpec (mov_r64_r64_effect_step 0x12897c 0x48 0xce (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x12897f [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x12897f) (movR64R64Effect 0x12897f 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x12897f 13 2).toInstrSpec (mov_r64_r64_effect_step 0x12897f 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x128982 [0x48, 0x89, 0xC2] (fun s => s.RIP = 0x128982) (movR64R64Effect 0x128982 2 0)
      [.gpr 0] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x128982 2 0).toInstrSpec (mov_r64_r64_effect_step 0x128982 0x48 0xc2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (6, 6), (14, 14), (15, 15)]) (p' := 0x128957) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (2, 2), (6, 6), (14, 14), (15, 15), (19, 55)]) (p' := 0x12895a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (2, 2), (6, 6), (7, 57), (14, 14), (15, 15), (19, 55)]) (p' := 0x128961) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (2, 2), (6, 6), (7, 57), (14, 14), (15, 15), (19, 55)]) (p' := 0x128968) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 61), (2, 2), (6, 6), (7, 57), (14, 14), (15, 15), (19, 55)]) (p' := 0x12896c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 61), (2, 2), (6, 6), (7, 57), (14, 14), (15, 15), (19, 55)]) (p' := 0x12896f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 61), (2, 2), (6, 6), (7, 57), (14, 14), (15, 15)]) (p' := 0x128972) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (1, 61), (2, 2), (6, 6), (14, 14), (15, 15)]) (p' := 0x128975) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 61), (2, 2), (6, 6), (14, 14), (15, 15)]) (p' := 0x128979) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 65), (1, 61), (2, 2), (6, 6), (14, 14), (15, 15)]) (p' := 0x12897c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 61), (2, 2), (14, 14), (15, 15)]) (p' := 0x12897f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 65), (1, 61), (2, 2), (14, 14), (15, 15)]) (p' := 0x128982) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 61), (14, 14), (15, 15)]) (p' := 0x128985) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128955 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128955 :=
  Rest.liftedBlock (rest_l128955 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128955 x hx)

theorem rest_l128989 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128989 bytes_l128989) (entryMap (live .l128989))
      4 0x128989 bytes_l128989 b_l128989 := by
  have f0 : InstrSpec 0x128989 [0x89, 0xC1] (fun s => s.RIP = 0x128989) (movR32R32Effect 0x128989 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x128989 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x128989 0xc1 (by decide)) pre_rip
  have f1 : InstrSpec 0x12898b [0xB0, 0x01] (fun s => s.RIP = 0x12898b) (movR8Imm8Effect 0x12898b 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x12898b 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x12898b 0xb0 (by decide) 0x1) pre_rip
  have f2 : InstrSpec 0x12898d [0x84, 0xC9] (fun s => s.RIP = 0x12898d) (testR8R8Effect 0x12898d 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x12898d 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x12898d 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12898b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12898d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12898f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel8_effect_step 0x12898f 5 0x9e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128989 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128989 :=
  Rest.liftedBlock (rest_l128989 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128989 x hx)

theorem rest_l128991 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128991 bytes_l128991) (entryMap (live .l128991))
      2 0x128991 bytes_l128991 b_l128991 := by
  have f0 : InstrSpec 0x128991 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x128991) (movR64R64Effect 0x128991 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128991 7 12).toInstrSpec (mov_r64_r64_effect_step 0x128991 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x128994 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x128994) (movR64R64Effect 0x128994 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128994 6 14).toInstrSpec (mov_r64_r64_effect_step 0x128994 0x4c 0xf6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(12, 12), (14, 14)]) (p' := 0x128994) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(12, 12), (14, 14)]) (p' := 0x128997) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128991 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128991 :=
  Rest.liftedBlock (rest_l128991 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128991 x hx)

theorem rest_l12899b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12899b bytes_l12899b) (entryMap (live .l12899b))
      1 0x12899b bytes_l12899b b_l12899b := by
  exact Rest.jmp (n := 53) (jmp_rel8_effect_step 0x12899b 0x92 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l12899b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12899b :=
  Rest.liftedBlock (rest_l12899b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12899b x hx)

theorem rest_l12899d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12899d bytes_l12899d) (entryMap (live .l12899d))
      2 0x12899d bytes_l12899d b_l12899d := by
  have f0 : InstrSpec 0x12899d [0x4D, 0x85, 0xFF] (fun s => s.RIP = 0x12899d) (testR64R64Effect 0x12899d 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x12899d 15 15).toInstrSpec (test_r64_r64_effect_step 0x12899d 0x4d 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (5, 5), (6, 6), (14, 14), (15, 15), (19, 53)]) (p' := 0x1289a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x1289a0 5 0x31) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l12899d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12899d :=
  Rest.liftedBlock (rest_l12899d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12899d x hx)

theorem rest_l1289a2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1289a2 bytes_l1289a2) (entryMap (live .l1289a2))
      7 0x1289a2 bytes_l1289a2 b_l1289a2 := by
  have f0 : InstrSpec 0x1289a2 [0x49, 0x8B, 0x3E] (LoadPre 0x1289a2 (fun s => AddrMode.addr (.base 14 .none) s (0x1289a2 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1289a2 7 (.base 14 .none))
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1289a2 7 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1289a2 0x49 (by decide) 7 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1289a5 [0x49, 0x8B, 0x4E, 0x08] (LoadPre 0x1289a5 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1289a5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1289a5 1 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1289a5 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1289a5 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1289a9 [0x48, 0x8D, 0x05, 0x81, 0xB2, 0x0D, 0x00] (fun s => s.RIP = 0x1289a9) (leaR64Effect 0x1289a9 0 (.rip 0xdb281))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1289a9 0 (.rip 0xdb281)).toInstrSpec (lea_r64_effect_step 0x1289a9 0x48 (by decide) 0 (.rip 0xdb281) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1289b0 [0x49, 0x89, 0xD4] (fun s => s.RIP = 0x1289b0) (movR64R64Effect 0x1289b0 12 2)
      [.gpr 2] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x1289b0 12 2).toInstrSpec (mov_r64_r64_effect_step 0x1289b0 0x49 0xd4 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1289b3 [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1289b3) (movR32Imm32Effect 0x1289b3 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x1289b3 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x1289b3 0xba (by decide) 0x2) pre_rip
  have f5 : InstrSpec 0x1289b8 [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x1289b8) (movR64R64Effect 0x1289b8 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1289b8 13 6).toInstrSpec (mov_r64_r64_effect_step 0x1289b8 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1289bb [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x1289bb) (movR64R64Effect 0x1289bb 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1289bb 6 0).toInstrSpec (mov_r64_r64_effect_step 0x1289bb 0x48 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(2, 2), (6, 6), (14, 14)]) (p' := 0x1289a5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(2, 2), (6, 6), (14, 14)]) (p' := 0x1289a9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (6, 6), (14, 14)]) (p' := 0x1289b0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (2, 2), (6, 6), (14, 14)]) (p' := 0x1289b3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (6, 6), (14, 14)]) (p' := 0x1289b8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (6, 6), (14, 14)]) (p' := 0x1289bb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 55), (14, 14)]) (p' := 0x1289be) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1289a2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1289a2 :=
  Rest.liftedBlock (rest_l1289a2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1289a2 x hx)

theorem rest_l1289c1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1289c1 bytes_l1289c1) (entryMap (live .l1289c1))
      6 0x1289c1 bytes_l1289c1 b_l1289c1 := by
  have f0 : InstrSpec 0x1289c1 [0x4C, 0x89, 0xEE] (fun s => s.RIP = 0x1289c1) (movR64R64Effect 0x1289c1 6 13)
      [.gpr 13] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1289c1 6 13).toInstrSpec (mov_r64_r64_effect_step 0x1289c1 0x4c 0xee (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1289c4 [0x4C, 0x89, 0xE2] (fun s => s.RIP = 0x1289c4) (movR64R64Effect 0x1289c4 2 12)
      [.gpr 12] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1289c4 2 12).toInstrSpec (mov_r64_r64_effect_step 0x1289c4 0x4c 0xe2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1289c7 [0x89, 0xC1] (fun s => s.RIP = 0x1289c7) (movR32R32Effect 0x1289c7 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1289c7 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x1289c7 0xc1 (by decide)) pre_rip
  have f3 : InstrSpec 0x1289c9 [0xB0, 0x01] (fun s => s.RIP = 0x1289c9) (movR8Imm8Effect 0x1289c9 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x1289c9 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x1289c9 0xb0 (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x1289cb [0x84, 0xC9] (fun s => s.RIP = 0x1289cb) (testR8R8Effect 0x1289cb 2 1 1)
      [.gpr 1, .gpr 1] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x1289cb 2 1 1).toInstrSpec (test_r8_r8_effect_step 0x1289cb 0xc9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1289c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1289c7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1289c9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1289cb) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1289cd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 63) (jcc_rel32_effect_step 0x1289cd 5 0xffffff5c) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1289c1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1289c1 :=
  Rest.liftedBlock (rest_l1289c1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1289c1 x hx)

theorem rest_l1289d3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1289d3 bytes_l1289d3) (entryMap (live .l1289d3))
      16 0x1289d3 bytes_l1289d3 b_l1289d3 := by
  have f0 : InstrSpec 0x1289d3 [0xC6, 0x45, 0xD7, 0x01] (StorePre 0x1289d3 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd7)) s (0x1289d3 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1289d3 (.base 5 (.d8 0xd7)) 0x1)
      [.gpr 5] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x1289d3 (.base 5 (.d8 0xd7)) 0x1).toInstrSpec (mov_m8_imm8_effect_step 0x1289d3 (.base 5 (.d8 0xd7)) (by decide) (by decide) (by decide) 0x1) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x1289d7 [0x49, 0x8B, 0x06] (LoadPre 0x1289d7 (fun s => AddrMode.addr (.base 14 .none) s (0x1289d7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1289d7 0 (.base 14 .none))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1289d7 0 (.base 14 .none)).toInstrSpec (mov_r64_m64_effect_step 0x1289d7 0x49 (by decide) 0 (.base 14 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1289da [0x49, 0x8B, 0x4E, 0x08] (LoadPre 0x1289da (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1289da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1289da 1 (.base 14 (.d8 0x8)))
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1289da 1 (.base 14 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x1289da 0x49 (by decide) 1 (.base 14 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1289de [0x48, 0x89, 0x45, 0xA0] (StorePre 0x1289de 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x1289de + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1289de 0 (.base 5 (.d8 0xa0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1289de 0 (.base 5 (.d8 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x1289de 0x48 (by decide) 0 (.base 5 (.d8 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1289e2 [0x48, 0x89, 0x4D, 0xA8] (StorePre 0x1289e2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x1289e2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1289e2 1 (.base 5 (.d8 0xa8)))
      [.gpr 1, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1289e2 1 (.base 5 (.d8 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x1289e2 0x48 (by decide) 1 (.base 5 (.d8 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1289e6 [0x48, 0x8D, 0x45, 0xD7] (fun s => s.RIP = 0x1289e6) (leaR64Effect 0x1289e6 0 (.base 5 (.d8 0xd7)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1289e6 0 (.base 5 (.d8 0xd7))).toInstrSpec (lea_r64_effect_step 0x1289e6 0x48 (by decide) 0 (.base 5 (.d8 0xd7)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1289ea [0x48, 0x89, 0x45, 0xB0] (StorePre 0x1289ea 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x1289ea + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1289ea 0 (.base 5 (.d8 0xb0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1289ea 0 (.base 5 (.d8 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x1289ea 0x48 (by decide) 0 (.base 5 (.d8 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1289ee [0x49, 0x8B, 0x46, 0x10] (LoadPre 0x1289ee (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1289ee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1289ee 0 (.base 14 (.d8 0x10)))
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1289ee 0 (.base 14 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x1289ee 0x49 (by decide) 0 (.base 14 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1289f2 [0x48, 0x89, 0x45, 0xC8] (StorePre 0x1289f2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x1289f2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1289f2 0 (.base 5 (.d8 0xc8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1289f2 0 (.base 5 (.d8 0xc8))).toInstrSpec (mov_m64_r64_effect_step 0x1289f2 0x48 (by decide) 0 (.base 5 (.d8 0xc8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1289f6 [0x48, 0x8D, 0x45, 0xA0] (fun s => s.RIP = 0x1289f6) (leaR64Effect 0x1289f6 0 (.base 5 (.d8 0xa0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1289f6 0 (.base 5 (.d8 0xa0))).toInstrSpec (lea_r64_effect_step 0x1289f6 0x48 (by decide) 0 (.base 5 (.d8 0xa0)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1289fa [0x48, 0x89, 0x45, 0xB8] (StorePre 0x1289fa 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x1289fa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1289fa 0 (.base 5 (.d8 0xb8)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x1289fa 0 (.base 5 (.d8 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x1289fa 0x48 (by decide) 0 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1289fe [0x48, 0x8D, 0x05, 0x83, 0xB3, 0x0D, 0x00] (fun s => s.RIP = 0x1289fe) (leaR64Effect 0x1289fe 0 (.rip 0xdb383))
      [] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1289fe 0 (.rip 0xdb383)).toInstrSpec (lea_r64_effect_step 0x1289fe 0x48 (by decide) 0 (.rip 0xdb383) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x128a05 [0x48, 0x89, 0x45, 0xC0] (StorePre 0x128a05 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128a05 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128a05 0 (.base 5 (.d8 0xc0)))
      [.gpr 0, .gpr 5] [] [.rip] :=
    (movM64R64Effect_footprint 0x128a05 0 (.base 5 (.d8 0xc0))).toInstrSpec (mov_m64_r64_effect_step 0x128a05 0x48 (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x128a09 [0x48, 0x8D, 0x45, 0xB8] (fun s => s.RIP = 0x128a09) (leaR64Effect 0x128a09 0 (.base 5 (.d8 0xb8)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x128a09 0 (.base 5 (.d8 0xb8))).toInstrSpec (lea_r64_effect_step 0x128a09 0x48 (by decide) 0 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x128a0d [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x128a0d) (movR64R64Effect 0x128a0d 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x128a0d 7 6).toInstrSpec (mov_r64_r64_effect_step 0x128a0d 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x128a10 [0x48, 0x89, 0xC6] (fun s => s.RIP = 0x128a10) (movR64R64Effect 0x128a10 6 0)
      [.gpr 0] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x128a10 6 0).toInstrSpec (mov_r64_r64_effect_step 0x128a10 0x48 0xc6 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(5, 5), (6, 6), (14, 14)]) (p' := 0x1289d7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (5, 5), (6, 6), (14, 14)]) (p' := 0x1289da) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x1289de) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 54), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x1289e2) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 54), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x1289e6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x1289ea) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 60), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x1289ee) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x1289f2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 63), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x1289f6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x1289fa) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x1289fe) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x128a05) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x128a09) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x128a0d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (1, 56), (5, 5), (6, 6), (14, 14)]) (p' := 0x128a10) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 72), (1, 56), (5, 5), (14, 14)]) (p' := 0x128a13) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l1289d3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1289d3 :=
  Rest.liftedBlock (rest_l1289d3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1289d3 x hx)

theorem rest_l128a16 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a16 bytes_l128a16) (entryMap (live .l128a16))
      2 0x128a16 bytes_l128a16 b_l128a16 := by
  have f0 : InstrSpec 0x128a16 [0x84, 0xC0] (fun s => s.RIP = 0x128a16) (testR8R8Effect 0x128a16 2 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR8R8Effect_footprint 0x128a16 2 0 0).toInstrSpec (test_r8_r8_effect_step 0x128a16 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a18) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x128a18 4 0x7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l128a16 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a16 :=
  Rest.liftedBlock (rest_l128a16 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a16 x hx)

theorem rest_l128a1a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a1a bytes_l128a1a) (entryMap (live .l128a1a))
      2 0x128a1a bytes_l128a1a b_l128a1a := by
  have f0 : InstrSpec 0x128a1a [0xB0, 0x01] (fun s => s.RIP = 0x128a1a) (movR8Imm8Effect 0x128a1a 2 0 0x1)
      [.gpr 0] [] [.reg 0, .rip] :=
    (movR8Imm8Effect_footprint 0x128a1a 2 0 0x1).toInstrSpec (mov_r8_imm8_effect_step 0x128a1a 0xb0 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x128a1c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 55) (jmp_rel32_effect_step 0x128a1c 0xffffff0e (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128a1a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a1a :=
  Rest.liftedBlock (rest_l128a1a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a1a x hx)

theorem rest_l128a21 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a21 bytes_l128a21) (entryMap (live .l128a21))
      4 0x128a21 bytes_l128a21 b_l128a21 := by
  have f0 : InstrSpec 0x128a21 [0x48, 0x8B, 0x7D, 0xB8] (LoadPre 0x128a21 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x128a21 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a21 7 (.base 5 (.d8 0xb8)))
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x128a21 7 (.base 5 (.d8 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x128a21 0x48 (by decide) 7 (.base 5 (.d8 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x128a25 [0x48, 0x8B, 0x45, 0xC0] (LoadPre 0x128a25 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128a25 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a25 0 (.base 5 (.d8 0xc0)))
      [.gpr 5] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x128a25 0 (.base 5 (.d8 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x128a25 0x48 (by decide) 0 (.base 5 (.d8 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x128a29 [0x48, 0x8D, 0x35, 0xFE, 0xB1, 0x0D, 0x00] (fun s => s.RIP = 0x128a29) (leaR64Effect 0x128a29 6 (.rip 0xdb1fe))
      [] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x128a29 6 (.rip 0xdb1fe)).toInstrSpec (lea_r64_effect_step 0x128a29 0x48 (by decide) 6 (.rip 0xdb1fe) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x128a30 [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x128a30) (movR32Imm32Effect 0x128a30 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x128a30 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x128a30 0xba (by decide) 0x2) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(5, 5)]) (p' := 0x128a25) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(5, 5)]) (p' := 0x128a29) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(5, 5)]) (p' := 0x128a30) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(5, 5)]) (p' := 0x128a35) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.cut

theorem block_l128a21 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a21 :=
  Rest.liftedBlock (rest_l128a21 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a21 x hx)

theorem rest_l128a38 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x128a38 bytes_l128a38) (entryMap (live .l128a38))
      1 0x128a38 bytes_l128a38 b_l128a38 := by
  exact Rest.jmp (n := 53) (jmp_rel32_effect_step 0x128a38 0xfffffef2 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l128a38 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l128a38 :=
  Rest.liftedBlock (rest_l128a38 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l128a38 x hx)

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

theorem_by block_l128910_eval :
    program.runBlock (dialect code) ⟨.l128910, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12892f_eval :
    program.runBlock (dialect code) ⟨.l12892f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12894a_eval :
    program.runBlock (dialect code) ⟨.l12894a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128955_eval :
    program.runBlock (dialect code) ⟨.l128955, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128989_eval :
    program.runBlock (dialect code) ⟨.l128989, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128991_eval :
    program.runBlock (dialect code) ⟨.l128991, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12899b_eval :
    program.runBlock (dialect code) ⟨.l12899b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12899d_eval :
    program.runBlock (dialect code) ⟨.l12899d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1289a2_eval :
    program.runBlock (dialect code) ⟨.l1289a2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1289c1_eval :
    program.runBlock (dialect code) ⟨.l1289c1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1289d3_eval :
    program.runBlock (dialect code) ⟨.l1289d3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a16_eval :
    program.runBlock (dialect code) ⟨.l128a16, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a1a_eval :
    program.runBlock (dialect code) ⟨.l128a1a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a21_eval :
    program.runBlock (dialect code) ⟨.l128a21, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l128a38_eval :
    program.runBlock (dialect code) ⟨.l128a38, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
