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

theorem rest_l120f30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120f30 bytes_l120f30) (entryMap (live .l120f30))
      8 0x120f30 bytes_l120f30 b_l120f30 := by
  have f0 : InstrSpec 0x120f30 [0x41, 0x57] (PushPre 0x120f30 2) (pushR64Effect 0x120f30 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120f30 2 15).toInstrSpec (push_r64_rex_effect_step 0x120f30 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x120f32 [0x41, 0x56] (PushPre 0x120f32 2) (pushR64Effect 0x120f32 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120f32 2 14).toInstrSpec (push_r64_rex_effect_step 0x120f32 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x120f34 [0x53] (PushPre 0x120f34 1) (pushR64Effect 0x120f34 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x120f34 1 3).toInstrSpec (push_r64_effect_step 0x120f34 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x120f35 [0x48, 0x81, 0xEC, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x120f35) (subR64Imm32Effect 0x120f35 4 0xf0)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x120f35 4 0xf0).toInstrSpec (sub_r64_imm32_effect_step 0x120f35 0x48 0xec 0xf0 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x120f3c [0x48, 0x89, 0xFB] (fun s => s.RIP = 0x120f3c) (movR64R64Effect 0x120f3c 3 7)
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x120f3c 3 7).toInstrSpec (mov_r64_r64_effect_step 0x120f3c 0x48 0xfb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x120f3f [0x0F, 0xB6, 0x06] (LoadPre 0x120f3f (fun s => AddrMode.addr (.base 6 .none) s (0x120f3f + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x120f3f 3 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x120f3f 3 0 (.base 6 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x120f3f 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x120f42 [0x83, 0xF8, 0x05] (fun s => s.RIP = 0x120f42) (cmpR32Imm8Effect 0x120f42 3 0 0x5)
      [.gpr 0] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x120f42 3 0 0x5).toInstrSpec (cmp_r32_imm8_effect_step 0x120f42 0xf8 0x5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f32) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f34) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f35) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 1), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f3c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 1), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f3f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f42) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 66) f6 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 67) (ρ' := [(0, 63), (1, 1), (3, 61), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f45) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 68) (jcc_rel32_effect_step 0x120f45 7 0x110) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l120f30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120f30 :=
  Rest.liftedBlock (rest_l120f30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120f30 x hx)

theorem rest_l120f4b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120f4b bytes_l120f4b) (entryMap (live .l120f4b))
      3 0x120f4b bytes_l120f4b b_l120f4b := by
  have f0 : InstrSpec 0x120f4b [0xB9, 0x2C, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x120f4b) (movR32Imm32Effect 0x120f4b 5 1 0x2c)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x120f4b 5 1 0x2c).toInstrSpec (mov_r32_imm32_effect_step 0x120f4b 0xb9 (by decide) 0x2c) pre_rip
  have f1 : InstrSpec 0x120f50 [0x0F, 0xA3, 0xC1] (fun s => s.RIP = 0x120f50) (btR32R32Effect 0x120f50 3 1 0)
      [.gpr 1, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.flags, .rip] :=
    (btR32R32Effect_footprint 0x120f50 3 1 0).toInstrSpec (bt_r32_r32_effect_step 0x120f50 0xc1 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f50) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.fresh (n := 55) f1 .CF (fun _ => rfl) (btR32R32Effect_fresh 0x120f50 3 1 0 _ (.head _)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f53) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x120f53 3 0x102) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l120f4b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120f4b :=
  Rest.liftedBlock (rest_l120f4b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120f4b x hx)

theorem rest_l120f59_2 [Bindings] (code : CodeMap) :
    Rest (n := 111) code lifted (codeRange 0x120f59 bytes_l120f59) [(0, 57), (1, 105), (2, 107), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x121053 bytes_l120f59_2 b_l120f59_2 := by
  have f40 : InstrSpec 0x121053 [0x41, 0xB7, 0x01] (fun s => s.RIP = 0x121053) (movR8Imm8Effect 0x121053 3 15 0x1)
      [.gpr 15] [] [.reg 15, .rip] :=
    (movR8Imm8Effect_footprint 0x121053 3 15 0x1).toInstrSpec (mov_r8_imm8_rex_effect_step 0x121053 0x41 (by decide) 0xb7 (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f40 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 57), (1, 105), (2, 107), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121056) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 113) (jmp_rel32_effect_step 0x121056 0xaa (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l120f59_1 [Bindings] (code : CodeMap) :
    Rest (n := 82) code lifted (codeRange 0x120f59 bytes_l120f59) [(0, 57), (1, 80), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      22 0x120fd7 bytes_l120f59_1 b_l120f59_1 := by
  have f20 : InstrSpec 0x120fd7 [0x48, 0x89, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00] (StorePre 0x120fd7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x120fd7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120fd7 1 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120fd7 1 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_m64_r64_effect_step 0x120fd7 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x120fdf [0x48, 0xC7, 0x84, 0x24, 0xBE, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x120fdf 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x120fdf + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x120fdf (.sib 4 none 0 (.d32 0xbe)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x120fdf (.sib 4 none 0 (.d32 0xbe)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x120fdf 0x48 (by decide) (.sib 4 none 0 (.d32 0xbe)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x120feb [0x8B, 0x0E] (LoadPre 0x120feb (fun s => AddrMode.addr (.base 6 .none) s (0x120feb + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x120feb 1 (.base 6 .none))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x120feb 1 (.base 6 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x120feb 1 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x120fed [0x8B, 0x56, 0x03] (LoadPre 0x120fed (fun s => AddrMode.addr (.base 6 (.d8 0x3)) s (0x120fed + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x120fed 2 (.base 6 (.d8 0x3)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x120fed 2 (.base 6 (.d8 0x3))).toInstrSpec (mov_r32_m32_low_effect_step 0x120fed 2 (.base 6 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x120ff0 [0x89, 0x54, 0x24, 0x0B] (StorePre 0x120ff0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x120ff0 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x120ff0 2 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x120ff0 2 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_m32_r32_low_effect_step 0x120ff0 2 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x120ff4 [0x89, 0x4C, 0x24, 0x08] (StorePre 0x120ff4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x120ff4 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x120ff4 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x120ff4 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x120ff4 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x120ff8 [0x48, 0x8B, 0x8C, 0x24, 0xBE, 0x00, 0x00, 0x00] (LoadPre 0x120ff8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x120ff8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x120ff8 1 (.sib 4 none 0 (.d32 0xbe)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120ff8 1 (.sib 4 none 0 (.d32 0xbe))).toInstrSpec (mov_r64_m64_effect_step 0x120ff8 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xbe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f27 : InstrSpec 0x121000 [0x48, 0x89, 0x4C, 0x24, 0x3E] (StorePre 0x121000 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x121000 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121000 1 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121000 1 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (mov_m64_r64_effect_step 0x121000 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x121005 [0x48, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x121005 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x121005 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121005 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x121005 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x121005 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x12100d [0x48, 0x89, 0x4C, 0x24, 0x38] (StorePre 0x12100d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12100d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12100d 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12100d 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x12100d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x121012 [0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x121012 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x121012 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121012 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x121012 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x121012 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f31 : InstrSpec 0x12101a [0x48, 0x89, 0x4C, 0x24, 0x30] (StorePre 0x12101a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12101a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12101a 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12101a 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x12101a 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x12101f [0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x12101f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x12101f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12101f 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12101f 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x12101f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f33 : InstrSpec 0x121027 [0x48, 0x89, 0x4C, 0x24, 0x28] (StorePre 0x121027 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x121027 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121027 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121027 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x121027 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x12102c [0x48, 0x8B, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x12102c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x12102c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x12102c 1 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12102c 1 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x12102c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x121034 [0x48, 0x89, 0x4C, 0x24, 0x20] (StorePre 0x121034 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x121034 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121034 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121034 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x121034 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x121039 [0x48, 0x8B, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x121039 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x121039 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121039 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x121039 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x121039 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x121041 [0x48, 0x8B, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x121041 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x121041 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x121041 2 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x121041 2 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x121041 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x121049 [0x48, 0x89, 0x54, 0x24, 0x18] (StorePre 0x121049 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x121049 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121049 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121049 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x121049 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x12104e [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x12104e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12104e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12104e 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12104e 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x12104e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 57), (1, 80), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fdf) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 57), (1, 80), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120feb) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 57), (1, 84), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fed) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f23 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 57), (1, 84), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ff0) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.exec (n := 88) (ρ' := [(0, 57), (1, 84), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ff4) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 57), (1, 84), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120ff8) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 57), (1, 90), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121000) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 57), (1, 90), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121005) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 57), (1, 93), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12100d) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 57), (1, 93), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121012) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 57), (1, 96), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12101a) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 57), (1, 96), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12101f) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f32 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 57), (1, 99), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121027) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 57), (1, 99), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12102c) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 57), (1, 102), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121034) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 57), (1, 102), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121039) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f36 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 57), (1, 105), (2, 86), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121041) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f37 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 57), (1, 105), (2, 107), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121049) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 57), (1, 105), (2, 107), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12104e) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 57), (1, 105), (2, 107), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121053) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l120f59_2 code

theorem rest_l120f59 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x120f59 bytes_l120f59) (entryMap (live .l120f59))
      42 0x120f59 bytes_l120f59 b_l120f59 := by
  have f0 : InstrSpec 0x120f59 [0x48, 0xC7, 0x44, 0x24, 0x76, 0x00, 0x00, 0x00, 0x00] (StorePre 0x120f59 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x120f59 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x120f59 (.sib 4 none 0 (.d8 0x76)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x120f59 (.sib 4 none 0 (.d8 0x76)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x120f59 0x48 (by decide) (.sib 4 none 0 (.d8 0x76)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x120f62 [0x48, 0xC7, 0x44, 0x24, 0x6E, 0x00, 0x00, 0x00, 0x00] (StorePre 0x120f62 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x120f62 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x120f62 (.sib 4 none 0 (.d8 0x6e)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x120f62 (.sib 4 none 0 (.d8 0x6e)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x120f62 0x48 (by decide) (.sib 4 none 0 (.d8 0x6e)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x120f6b [0x48, 0xC7, 0x44, 0x24, 0x66, 0x00, 0x00, 0x00, 0x00] (StorePre 0x120f6b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x120f6b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x120f6b (.sib 4 none 0 (.d8 0x66)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x120f6b (.sib 4 none 0 (.d8 0x66)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x120f6b 0x48 (by decide) (.sib 4 none 0 (.d8 0x66)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x120f74 [0x48, 0xC7, 0x44, 0x24, 0x5E, 0x00, 0x00, 0x00, 0x00] (StorePre 0x120f74 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x120f74 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x120f74 (.sib 4 none 0 (.d8 0x5e)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x120f74 (.sib 4 none 0 (.d8 0x5e)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x120f74 0x48 (by decide) (.sib 4 none 0 (.d8 0x5e)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x120f7d [0x8B, 0x46, 0x07] (LoadPre 0x120f7d (fun s => AddrMode.addr (.base 6 (.d8 0x7)) s (0x120f7d + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x120f7d 0 (.base 6 (.d8 0x7)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x120f7d 0 (.base 6 (.d8 0x7))).toInstrSpec (mov_r32_m32_low_effect_step 0x120f7d 0 (.base 6 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x120f80 [0x48, 0x8B, 0x4E, 0x19] (LoadPre 0x120f80 (fun s => AddrMode.addr (.base 6 (.d8 0x19)) s (0x120f80 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120f80 1 (.base 6 (.d8 0x19)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120f80 1 (.base 6 (.d8 0x19))).toInstrSpec (mov_r64_m64_effect_step 0x120f80 0x48 (by decide) 1 (.base 6 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x120f84 [0x48, 0x89, 0x4C, 0x24, 0x56] (StorePre 0x120f84 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x120f84 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120f84 1 (.sib 4 none 0 (.d8 0x56)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120f84 1 (.sib 4 none 0 (.d8 0x56))).toInstrSpec (mov_m64_r64_effect_step 0x120f84 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x56)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x120f89 [0x48, 0x8B, 0x4E, 0x13] (LoadPre 0x120f89 (fun s => AddrMode.addr (.base 6 (.d8 0x13)) s (0x120f89 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120f89 1 (.base 6 (.d8 0x13)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120f89 1 (.base 6 (.d8 0x13))).toInstrSpec (mov_r64_m64_effect_step 0x120f89 0x48 (by decide) 1 (.base 6 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x120f8d [0x48, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x120f8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120f8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x120f8d 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120f8d 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x120f8d 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x120f92 [0x48, 0x8B, 0x4E, 0x0B] (LoadPre 0x120f92 (fun s => AddrMode.addr (.base 6 (.d8 0xb)) s (0x120f92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x120f92 1 (.base 6 (.d8 0xb)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120f92 1 (.base 6 (.d8 0xb))).toInstrSpec (mov_r64_m64_effect_step 0x120f92 0x48 (by decide) 1 (.base 6 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x120f96 [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (StorePre 0x120f96 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x120f96 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120f96 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120f96 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_m64_r64_effect_step 0x120f96 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x120f9e [0x48, 0x8B, 0x4C, 0x24, 0x60] (LoadPre 0x120f9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x120f9e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120f9e 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120f9e 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x120f9e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x120fa3 [0x48, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00] (StorePre 0x120fa3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x120fa3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120fa3 1 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120fa3 1 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_m64_r64_effect_step 0x120fa3 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x120fab [0x48, 0x8B, 0x4C, 0x24, 0x68] (LoadPre 0x120fab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x120fab + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120fab 1 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120fab 1 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x120fab 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x120fb0 [0x48, 0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x120fb0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x120fb0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120fb0 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120fb0 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m64_r64_effect_step 0x120fb0 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x120fb8 [0x48, 0x8B, 0x4C, 0x24, 0x70] (LoadPre 0x120fb8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x120fb8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120fb8 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120fb8 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x120fb8 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x120fbd [0x48, 0x89, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00] (StorePre 0x120fbd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x120fbd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120fbd 1 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120fbd 1 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_m64_r64_effect_step 0x120fbd 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x120fc5 [0x48, 0x8B, 0x4C, 0x24, 0x50] (LoadPre 0x120fc5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x120fc5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120fc5 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120fc5 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x120fc5 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x120fca [0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00] (StorePre 0x120fca 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x120fca + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x120fca 1 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x120fca 1 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_m64_r64_effect_step 0x120fca 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x120fd2 [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x120fd2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x120fd2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x120fd2 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x120fd2 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x120fd2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f62) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f6b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f74) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f7d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f80) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f84) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f89) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 57), (1, 62), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f8d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 62), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f92) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 65), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f96) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 57), (1, 65), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120f9e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 57), (1, 68), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fa3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 68), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fab) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 71), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fb0) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 57), (1, 71), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fb8) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 57), (1, 74), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fbd) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 57), (1, 74), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fc5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f17 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 77), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fca) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 57), (1, 77), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fd2) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 57), (1, 80), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x120fd7) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l120f59_1 code

theorem block_l120f59 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l120f59 :=
  Rest.liftedBlock (rest_l120f59 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l120f59 x hx)

theorem rest_l12105b_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x12105b bytes_l12105b) [(0, 57), (1, 59), (2, 89), (3, 3), (4, 4), (5, 5), (6, 91), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]
      15 0x1210a2 bytes_l12105b_1 b_l12105b_1 := by
  have f20 : InstrSpec 0x1210a2 [0x48, 0x31, 0xC6] (fun s => s.RIP = 0x1210a2) (xorR64R64Effect 0x1210a2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1210a2 6 0).toInstrSpec (xor_r64_r64_effect_step 0x1210a2 0x48 0xc6 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1210a5 [0x48, 0x0F, 0x45, 0xD0] (fun s => s.RIP = 0x1210a5) (atFlags (condHolds 5) (cmovR64R64Effect 0x1210a5 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x1210a5 4 2 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x1210a5 5 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f22 : InstrSpec 0x1210a9 [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x1210a9) (movzxR32R8Effect 0x1210a9 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x1210a9 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x1210a9 0xd2 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1210ac [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x1210ac) (xorR32R32Effect 0x1210ac 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1210ac 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x1210ac 0x45 0xff (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x1210af [0x66, 0x31, 0xCA] (fun s => s.RIP = 0x1210af) (xorR16R16Effect 0x1210af 3 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR16R16Effect_footprint 0x1210af 3 2 1).toInstrSpec (xor_r16_r16_effect_step 0x1210af 0xca (by decide)) pre_rip
  have f25 : InstrSpec 0x1210b2 [0x44, 0x0F, 0x44, 0xF9] (fun s => s.RIP = 0x1210b2) (atFlags (condHolds 4) (cmovR32R32Effect 0x1210b2 4 15 1))
      [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 15, .rip] :=
    (cmovR32R32Effect_footprint 0x1210b2 4 15 1 4).toInstrSpec (StepEffect.atFlags fun c => (cmov_r32_r32_rex_effect_step 0x1210b2 4 0x44 (by decide) 0xf9 (by decide) c)) pre_rip
  have f26 : InstrSpec 0x1210b6 [0xC7, 0x44, 0x24, 0x0B, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1210b6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1210b6 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x1210b6 8 (.sib 4 none 0 (.d8 0xb)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1210b6 8 (.sib 4 none 0 (.d8 0xb)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x1210b6 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x1210be [0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1210be 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1210be + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x1210be 8 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM32Imm32Effect_footprint 0x1210be 8 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m32_imm32_effect_step 0x1210be (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x1210c6 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1210c6 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1210c6 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1210c6 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1210c6 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1210c6 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x1210cf [0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1210cf 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1210cf + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1210cf (.sib 4 none 0 (.d8 0x18)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1210cf (.sib 4 none 0 (.d8 0x18)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1210cf 0x48 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x1210d8 [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1210d8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1210d8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1210d8 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1210d8 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1210d8 0x48 (by decide) (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x1210e1 [0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1210e1 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1210e1 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1210e1 (.sib 4 none 0 (.d8 0x28)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1210e1 (.sib 4 none 0 (.d8 0x28)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1210e1 0x48 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x1210ea [0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1210ea 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1210ea + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1210ea (.sib 4 none 0 (.d8 0x30)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1210ea (.sib 4 none 0 (.d8 0x30)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1210ea 0x48 (by decide) (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x1210f3 [0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1210f3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1210f3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1210f3 (.sib 4 none 0 (.d8 0x38)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1210f3 (.sib 4 none 0 (.d8 0x38)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1210f3 0x48 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x1210fc [0x48, 0xC7, 0x44, 0x24, 0x3E, 0x00, 0x00, 0x00, 0x00] (StorePre 0x1210fc 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x1210fc + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1210fc (.sib 4 none 0 (.d8 0x3e)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x1210fc (.sib 4 none 0 (.d8 0x3e)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x1210fc 0x48 (by decide) (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 57), (1, 59), (2, 89), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210a5) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 57), (1, 59), (2, 95), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210a9) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 57), (1, 59), (2, 97), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210ac) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 57), (1, 59), (2, 97), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 99), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210af) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 99), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210b2) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 103), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210b6) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.exec (n := 105) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 103), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210be) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 106) (RestInside.exec (n := 106) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 103), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210c6) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 103), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210cf) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.exec (n := 108) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 103), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210d8) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 109) (RestInside.exec (n := 109) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 103), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210e1) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 103), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210ea) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.exec (n := 111) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 103), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210f3) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 103), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210fc) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 103), (19, 101), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121105) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 114) (by decide) rfl

theorem rest_l12105b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x12105b bytes_l12105b) (entryMap (live .l12105b))
      35 0x12105b bytes_l12105b b_l12105b := by
  have f0 : InstrSpec 0x12105b [0x48, 0x8B, 0x16] (LoadPre 0x12105b (fun s => AddrMode.addr (.base 6 .none) s (0x12105b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12105b 2 (.base 6 .none))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x12105b 2 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x12105b 0x48 (by decide) 2 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12105e [0x48, 0x8B, 0x7E, 0x08] (LoadPre 0x12105e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x12105e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12105e 7 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12105e 7 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x12105e 0x48 (by decide) 7 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x121062 [0x31, 0xC0] (fun s => s.RIP = 0x121062) (xorR32R32Effect 0x121062 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x121062 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x121062 0xc0 (by decide)) pre_rip
  have f3 : InstrSpec 0x121064 [0x66, 0xB9, 0x01, 0x00] (fun s => s.RIP = 0x121064) (movR16Imm16Effect 0x121064 4 1 0x1)
      [.gpr 1] [] [.reg 1, .rip] :=
    (movR16Imm16Effect_footprint 0x121064 4 1 0x1).toInstrSpec (mov_r16_imm16_effect_step 0x121064 0xb9 (by decide) 0x1) pre_rip
  have f4 : InstrSpec 0x121068 [0x66, 0x41, 0xB8, 0x01, 0x00] (fun s => s.RIP = 0x121068) (movR16Imm16Effect 0x121068 5 8 0x1)
      [.gpr 8] [] [.reg 8, .rip] :=
    (movR16Imm16Effect_footprint 0x121068 5 8 0x1).toInstrSpec (mov_r16_imm16_rex_effect_step 0x121068 0x41 (by decide) 0xb8 (by decide) 0x1) pre_rip
  have f5 : InstrSpec 0x12106d [0x48, 0x31, 0xC2] (fun s => s.RIP = 0x12106d) (xorR64R64Effect 0x12106d 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x12106d 2 0).toInstrSpec (xor_r64_r64_effect_step 0x12106d 0x48 0xc2 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x121070 [0x4C, 0x0F, 0x45, 0xC0] (fun s => s.RIP = 0x121070) (atFlags (condHolds 5) (cmovR64R64Effect 0x121070 4 8 0))
      [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 8, .rip] :=
    (cmovR64R64Effect_footprint 0x121070 4 8 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x121070 5 0x4c (by decide) 0xc0 (by decide) c)) pre_rip
  have f7 : InstrSpec 0x121074 [0x41, 0x0F, 0xB6, 0xD0] (fun s => s.RIP = 0x121074) (movzxR32R8Effect 0x121074 4 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x121074 4 2 8).toInstrSpec (movzx_r32_r8_rex_effect_step 0x121074 0x41 (by decide) 0xd0 (by decide)) pre_rip
  have f8 : InstrSpec 0x121078 [0x48, 0x31, 0xC7] (fun s => s.RIP = 0x121078) (xorR64R64Effect 0x121078 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x121078 7 0).toInstrSpec (xor_r64_r64_effect_step 0x121078 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x12107b [0x48, 0x0F, 0x45, 0xD0] (fun s => s.RIP = 0x12107b) (atFlags (condHolds 5) (cmovR64R64Effect 0x12107b 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x12107b 4 2 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x12107b 5 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f10 : InstrSpec 0x12107f [0x48, 0x8B, 0x7E, 0x10] (LoadPre 0x12107f (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x12107f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12107f 7 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12107f 7 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x12107f 0x48 (by decide) 7 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x121083 [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x121083) (movzxR32R8Effect 0x121083 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x121083 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x121083 0xd2 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x121086 [0x48, 0x31, 0xC7] (fun s => s.RIP = 0x121086) (xorR64R64Effect 0x121086 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x121086 7 0).toInstrSpec (xor_r64_r64_effect_step 0x121086 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x121089 [0x48, 0x0F, 0x45, 0xD0] (fun s => s.RIP = 0x121089) (atFlags (condHolds 5) (cmovR64R64Effect 0x121089 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x121089 4 2 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x121089 5 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f14 : InstrSpec 0x12108d [0x48, 0x8B, 0x7E, 0x18] (LoadPre 0x12108d (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12108d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12108d 7 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x12108d 7 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12108d 0x48 (by decide) 7 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x121091 [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x121091) (movzxR32R8Effect 0x121091 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x121091 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x121091 0xd2 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x121094 [0x48, 0x31, 0xC7] (fun s => s.RIP = 0x121094) (xorR64R64Effect 0x121094 7 0)
      [.gpr 7, .gpr 0] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x121094 7 0).toInstrSpec (xor_r64_r64_effect_step 0x121094 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x121097 [0x48, 0x0F, 0x45, 0xD0] (fun s => s.RIP = 0x121097) (atFlags (condHolds 5) (cmovR64R64Effect 0x121097 4 2 0))
      [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 2, .rip] :=
    (cmovR64R64Effect_footprint 0x121097 4 2 0 5).toInstrSpec (StepEffect.atFlags fun c => (cmov_r64_r64_effect_step 0x121097 5 0x48 (by decide) 0xd0 (by decide) c)) pre_rip
  have f18 : InstrSpec 0x12109b [0x0F, 0xB6, 0xD2] (fun s => s.RIP = 0x12109b) (movzxR32R8Effect 0x12109b 3 2 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (movzxR32R8Effect_footprint 0x12109b 3 2 2).toInstrSpec (movzx_r32_r8_effect_step 0x12109b 0xd2 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x12109e [0x0F, 0xB6, 0x76, 0x20] (LoadPre 0x12109e (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x12109e + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x12109e 4 6 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x12109e 4 6 (.base 6 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x12109e 6 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12105e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121062) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121064) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (1, 59), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121068) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (1, 59), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 61), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12106d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 61), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121070) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (1, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121074) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 57), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121078) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 57), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 6), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12107b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 57), (1, 59), (2, 71), (3, 3), (4, 4), (5, 5), (6, 6), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12107f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 57), (1, 59), (2, 71), (3, 3), (4, 4), (5, 5), (6, 6), (7, 73), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121083) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 57), (1, 59), (2, 75), (3, 3), (4, 4), (5, 5), (6, 6), (7, 73), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121086) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 57), (1, 59), (2, 75), (3, 3), (4, 4), (5, 5), (6, 6), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121089) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 57), (1, 59), (2, 79), (3, 3), (4, 4), (5, 5), (6, 6), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12108d) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 57), (1, 59), (2, 79), (3, 3), (4, 4), (5, 5), (6, 6), (7, 81), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121091) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 57), (1, 59), (2, 83), (3, 3), (4, 4), (5, 5), (6, 6), (7, 81), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121094) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 57), (1, 59), (2, 83), (3, 3), (4, 4), (5, 5), (6, 6), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121097) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 57), (1, 59), (2, 87), (3, 3), (4, 4), (5, 5), (6, 6), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12109b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 57), (1, 59), (2, 89), (3, 3), (4, 4), (5, 5), (6, 6), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12109e) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 57), (1, 59), (2, 89), (3, 3), (4, 4), (5, 5), (6, 91), (8, 65), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 85), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1210a2) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l12105b_1 code

theorem block_l12105b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l12105b :=
  Rest.liftedBlock (rest_l12105b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l12105b x hx)

theorem rest_l121105_1 [Bindings] (code : CodeMap) :
    Rest (n := 83) code lifted (codeRange 0x121105 bytes_l121105) [(0, 78), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 81), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      3 0x12116a bytes_l121105_1 b_l121105_1 := by
  have f20 : InstrSpec 0x12116a [0x48, 0x8D, 0x74, 0x24, 0x48] (fun s => s.RIP = 0x12116a) (leaR64Effect 0x12116a 6 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x12116a 6 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (lea_r64_effect_step 0x12116a 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x12116f [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x12116f) (movR64R64Effect 0x12116f 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x12116f 7 14).toInstrSpec (mov_r64_r64_effect_step 0x12116f 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x121172 [0xE8, 0x09, 0x03, 0x00, 0x00] (PushPre 0x121172 5) (callEffect (fun _ => 0x121480) 0x121177)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x121172 0x121480 0x121177).toInstrSpec (call_rel32_effect_step 0x121172 0x309 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 78), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 83), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 81), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12116f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 78), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (6, 83), (7, 85), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 81), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121172) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f22 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 78), (1, 62), (2, 55), (3, 3), (4, 87), (5, 5), (6, 83), (7, 85), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 81), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121480) f22 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem rest_l121105 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121105 bytes_l121105) (entryMap (live .l121105))
      23 0x121105 bytes_l121105 b_l121105 := by
  have f0 : InstrSpec 0x121105 [0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x121105 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x121105 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x121105 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x121105 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x121105 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x121109 [0x8B, 0x54, 0x24, 0x0B] (LoadPre 0x121109 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x121109 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x121109 2 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x121109 2 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_r32_m32_low_effect_step 0x121109 2 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x12110d [0x89, 0x54, 0x24, 0x4B] (StorePre 0x12110d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x12110d + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x12110d 2 (.sib 4 none 0 (.d8 0x4b)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x12110d 2 (.sib 4 none 0 (.d8 0x4b))).toInstrSpec (mov_m32_r32_low_effect_step 0x12110d 2 (.sib 4 none 0 (.d8 0x4b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x121111 [0x89, 0x4C, 0x24, 0x48] (StorePre 0x121111 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x121111 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121111 1 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x121111 1 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m32_r32_low_effect_step 0x121111 1 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x121115 [0x89, 0x44, 0x24, 0x4F] (StorePre 0x121115 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x121115 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x121115 0 (.sib 4 none 0 (.d8 0x4f)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x121115 0 (.sib 4 none 0 (.d8 0x4f))).toInstrSpec (mov_m32_r32_low_effect_step 0x121115 0 (.sib 4 none 0 (.d8 0x4f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x121119 [0x48, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x121119 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x121119 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121119 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121119 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x121119 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x12111e [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x12111e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12111e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12111e 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x12111e 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x12111e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x121123 [0x48, 0x89, 0x44, 0x24, 0x53] (StorePre 0x121123 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x121123 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121123 0 (.sib 4 none 0 (.d8 0x53)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121123 0 (.sib 4 none 0 (.d8 0x53))).toInstrSpec (mov_m64_r64_effect_step 0x121123 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x53)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x121128 [0x48, 0x89, 0x4C, 0x24, 0x5B] (StorePre 0x121128 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x121128 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121128 1 (.sib 4 none 0 (.d8 0x5b)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121128 1 (.sib 4 none 0 (.d8 0x5b))).toInstrSpec (mov_m64_r64_effect_step 0x121128 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x5b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x12112d [0x48, 0x8B, 0x44, 0x24, 0x20] (LoadPre 0x12112d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x12112d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12112d 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12112d 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x12112d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x121132 [0x48, 0x89, 0x44, 0x24, 0x63] (StorePre 0x121132 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x63)) s (0x121132 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121132 0 (.sib 4 none 0 (.d8 0x63)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121132 0 (.sib 4 none 0 (.d8 0x63))).toInstrSpec (mov_m64_r64_effect_step 0x121132 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x63)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x121137 [0x48, 0x8B, 0x44, 0x24, 0x28] (LoadPre 0x121137 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x121137 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121137 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121137 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x121137 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x12113c [0x48, 0x89, 0x44, 0x24, 0x6B] (StorePre 0x12113c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6b)) s (0x12113c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12113c 0 (.sib 4 none 0 (.d8 0x6b)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12113c 0 (.sib 4 none 0 (.d8 0x6b))).toInstrSpec (mov_m64_r64_effect_step 0x12113c 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x6b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x121141 [0x48, 0x8B, 0x44, 0x24, 0x30] (LoadPre 0x121141 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x121141 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121141 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121141 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x121141 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x121146 [0x48, 0x89, 0x44, 0x24, 0x73] (StorePre 0x121146 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x73)) s (0x121146 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121146 0 (.sib 4 none 0 (.d8 0x73)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121146 0 (.sib 4 none 0 (.d8 0x73))).toInstrSpec (mov_m64_r64_effect_step 0x121146 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x73)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x12114b [0x48, 0x8B, 0x44, 0x24, 0x38] (LoadPre 0x12114b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12114b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12114b 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x12114b 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x12114b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x121150 [0x48, 0x89, 0x44, 0x24, 0x7B] (StorePre 0x121150 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7b)) s (0x121150 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x121150 0 (.sib 4 none 0 (.d8 0x7b)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x121150 0 (.sib 4 none 0 (.d8 0x7b))).toInstrSpec (mov_m64_r64_effect_step 0x121150 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x7b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x121155 [0x48, 0x8B, 0x44, 0x24, 0x3E] (LoadPre 0x121155 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x121155 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x121155 0 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x121155 0 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (mov_r64_m64_effect_step 0x121155 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x12115a [0x48, 0x89, 0x84, 0x24, 0x81, 0x00, 0x00, 0x00] (StorePre 0x12115a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x81)) s (0x12115a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12115a 0 (.sib 4 none 0 (.d32 0x81)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x12115a 0 (.sib 4 none 0 (.d32 0x81))).toInstrSpec (mov_m64_r64_effect_step 0x12115a 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x81)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x121162 [0x4C, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x121162) (leaR64Effect 0x121162 14 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x121162 14 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (lea_r64_effect_step 0x121162 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121109) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12110d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121111) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121115) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121119) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (1, 53), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12111e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 60), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121123) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 60), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121128) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 60), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12112d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121132) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121137) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12113c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 69), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121141) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121146) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12114b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121150) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 75), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121155) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 78), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12115a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 78), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121162) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f19 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 78), (1, 62), (2, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 81), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12116a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l121105_1 code

theorem block_l121105 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121105 :=
  Rest.liftedBlock (rest_l121105 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121105 x hx)

theorem rest_l121177 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121177 bytes_l121177) (entryMap (live .l121177))
      7 0x121177 bytes_l121177 b_l121177 := by
  have f0 : InstrSpec 0x121177 [0x44, 0x22, 0xBC, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x121177 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x121177 + BitVec.ofNat 64 8)) 1) (andR8M8Effect 0x121177 8 15 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 15, .gpr 4] [] [.reg 15, .flags, .rip] :=
    (andR8M8Effect_footprint 0x121177 8 15 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (and_r8_m8_rex_effect_step 0x121177 0x44 (by decide) 7 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x12117f [0xB9, 0x0B, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12117f) (movR32Imm32Effect 0x12117f 5 1 0xb)
      [] [] [.reg 1, .rip] :=
    (movR32Imm32Effect_footprint 0x12117f 5 1 0xb).toInstrSpec (mov_r32_imm32_effect_step 0x12117f 0xb9 (by decide) 0xb) pre_rip
  have f2 : InstrSpec 0x121184 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x121184) (movR64R64Effect 0x121184 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x121184 7 3).toInstrSpec (mov_r64_r64_effect_step 0x121184 0x48 0xdf (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x121187 [0x4C, 0x89, 0xF6] (fun s => s.RIP = 0x121187) (movR64R64Effect 0x121187 6 14)
      [.gpr 14] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x121187 6 14).toInstrSpec (mov_r64_r64_effect_step 0x121187 0x4c 0xf6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x12118a [0xF3, 0x48, 0xA5] (RepPre 0x12118a (RepMovsqPre 0x12118a)) (repMovsqEffect 0x12118a)
      [.gpr 6, .gpr 7, .gpr 1, .df] [] [.reg 6, .reg 7, .reg 1, .rip] :=
    (repMovsqEffect_footprint 0x12118a).toInstrSpecOfRuns (rep_movsq_runs hstride 0x12118a 0x48 (by decide)) (RepMovsOk.of_stateOf RepMovsqPre.iff (by lift_reads) (by lift_reads) (by lift_reads) (by lift_reads))
  have f5 : InstrSpec 0x12118d [0x41, 0x0F, 0xB6, 0xFF] (fun s => s.RIP = 0x12118d) (movzxR32R8Effect 0x12118d 4 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movzxR32R8Effect_footprint 0x12118d 4 7 15).toInstrSpec (movzx_r32_r8_rex_effect_step 0x12118d 0x41 (by decide) 0xff (by decide)) pre_rip
  have f6 : InstrSpec 0x121191 [0xE8, 0xBA, 0x6B, 0x00, 0x00] (PushPre 0x121191 5) (callEffect (fun _ => 0x127d50) 0x121196)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x121191 0x127d50 0x121196).toInstrSpec (call_rel32_effect_step 0x121191 0x6bba (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12117f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121184) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121187) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12118a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(1, 62), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12118d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(1, 62), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 64), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121191) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(1, 62), (2, 2), (3, 3), (4, 66), (5, 5), (6, 61), (7, 64), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x127d50) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 68) (by decide) (by decide) rfl rfl

theorem block_l121177 [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121177 :=
  Rest.liftedBlock (rest_l121177 hstride code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121177 x hx)

theorem rest_l121196 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x121196 bytes_l121196) (entryMap (live .l121196))
      7 0x121196 bytes_l121196 b_l121196 := by
  have f0 : InstrSpec 0x121196 [0x88, 0x43, 0x58] (StorePre 0x121196 3 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x121196 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x121196 3 0 (.base 3 (.d8 0x58)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM8R8Effect_footprint 0x121196 3 0 (.base 3 (.d8 0x58))).toInstrSpec (mov_m8_r8_effect_step 0x121196 0 (by decide) (.base 3 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x121199 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x121199) (movR64R64Effect 0x121199 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x121199 0 3).toInstrSpec (mov_r64_r64_effect_step 0x121199 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x12119c [0x48, 0x81, 0xC4, 0xF0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x12119c) (addR64Imm32Effect 0x12119c 4 0xf0)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x12119c 4 0xf0).toInstrSpec (add_r64_imm32_effect_step 0x12119c 0x48 0xc4 0xf0 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1211a3 [0x5B] (PopPre 0x1211a3) (popR64Effect 0x1211a3 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1211a3 1 3).toInstrSpec (pop_r64_effect_step 0x1211a3 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1211a4 [0x41, 0x5E] (PopPre 0x1211a4) (popR64Effect 0x1211a4 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1211a4 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1211a4 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1211a6 [0x41, 0x5F] (PopPre 0x1211a6) (popR64Effect 0x1211a6 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1211a6 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1211a6 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1211a8 [0xC3] (RetPre 0x1211a8) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1211a8).toInstrSpec (ret_effect_step 0x1211a8) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x121199) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x12119c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211a3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211a4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211a6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1211a8) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f6 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 69) (ρ' := [(0, 54), (1, 1), (2, 2), (3, 58), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) f6 (by decide) rfl rfl rfl (by decide)

theorem block_l121196 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l121196 :=
  Rest.liftedBlock (rest_l121196 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l121196 x hx)

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

theorem_by block_l120f30_eval :
    program.runBlock (dialect code) ⟨.l120f30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120f4b_eval :
    program.runBlock (dialect code) ⟨.l120f4b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l120f59_eval :
    program.runBlock (dialect code) ⟨.l120f59, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l12105b_eval :
    program.runBlock (dialect code) ⟨.l12105b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121105_eval :
    program.runBlock (dialect code) ⟨.l121105, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121177_eval :
    program.runBlock (dialect code) ⟨.l121177, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l121196_eval :
    program.runBlock (dialect code) ⟨.l121196, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Signing.LIR
