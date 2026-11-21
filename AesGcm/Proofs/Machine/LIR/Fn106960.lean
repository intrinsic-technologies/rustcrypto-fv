import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l106960 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106960 bytes_l106960) (entryMap (live .l106960))
      14 0x106960 bytes_l106960 b_l106960 := by
  have f0 : InstrSpec 0x106960 [0x55] (PushPre 0x106960 1) (pushR64Effect 0x106960 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106960 1 5).toInstrSpec (push_r64_effect_step 0x106960 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x106961 [0x41, 0x57] (PushPre 0x106961 2) (pushR64Effect 0x106961 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106961 2 15).toInstrSpec (push_r64_rex_effect_step 0x106961 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x106963 [0x41, 0x56] (PushPre 0x106963 2) (pushR64Effect 0x106963 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106963 2 14).toInstrSpec (push_r64_rex_effect_step 0x106963 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x106965 [0x41, 0x55] (PushPre 0x106965 2) (pushR64Effect 0x106965 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106965 2 13).toInstrSpec (push_r64_rex_effect_step 0x106965 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x106967 [0x41, 0x54] (PushPre 0x106967 2) (pushR64Effect 0x106967 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106967 2 12).toInstrSpec (push_r64_rex_effect_step 0x106967 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x106969 [0x53] (PushPre 0x106969 1) (pushR64Effect 0x106969 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x106969 1 3).toInstrSpec (push_r64_effect_step 0x106969 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10696a [0x48, 0x83, 0xEC, 0x48] (fun s => s.RIP = 0x10696a) (subR64Imm8Effect 0x10696a 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10696a 4 0x48).toInstrSpec (sub_r64_imm8_effect_step 0x10696a 0x48 0xec 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10696e [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x10696e) (movR64R64Effect 0x10696e 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10696e 3 6).toInstrSpec (mov_r64_r64_effect_step 0x10696e 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x106971 [0x48, 0x89, 0x7C, 0x24, 0x40] (StorePre 0x106971 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106971 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106971 7 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106971 7 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x106971 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x106976 [0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00] (StorePre 0x106976 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106976 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106976 (.sib 4 none 0 (.d8 0x10)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x106976 (.sib 4 none 0 (.d8 0x10)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x106976 0x48 (by decide) (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10697f [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10697f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10697f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10697f (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10697f (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10697f 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x106988 [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x106988) (leaR64Effect 0x106988 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106988 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106988 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10698d [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10698d) (movR32Imm32Effect 0x10698d 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10698d 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x10698d 0xbe (by decide) 0x8) pre_rip
  have f13 : InstrSpec 0x106992 [0xE8, 0x59, 0x36, 0x00, 0x00] (PushPre 0x106992 5) (callEffect (fun _ => 0x109ff0) 0x106997)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106992 0x109ff0 0x106997).toInstrSpec (call_rel32_effect_step 0x106992 0x3659 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106961) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106963) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106965) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106967) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106969) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10696a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10696e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106971) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106976) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10697f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106988) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10698d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 74), (7, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106992) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(2, 2), (3, 67), (4, 76), (5, 5), (6, 74), (7, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff0) f13 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 78) (by decide) (by decide) rfl rfl

theorem block_l106960 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106960 :=
  Rest.liftedBlock (rest_l106960 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106960 x hx)

theorem rest_l106997 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106997 bytes_l106997) (entryMap (live .l106997))
      18 0x106997 bytes_l106997 b_l106997 := by
  have f0 : InstrSpec 0x106997 [0x0F, 0xB7, 0x03] (LoadPre 0x106997 (fun s => AddrMode.addr (.base 3 .none) s (0x106997 + BitVec.ofNat 64 3)) 2) (movzxR32M16Effect 0x106997 3 0 (.base 3 .none))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106997 3 0 (.base 3 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x106997 0 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10699a [0x66, 0x31, 0x44, 0x24, 0x08] (StorePre 0x10699a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10699a + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10699a 5 16 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x10699a 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m16_r16_effect_step 0x10699a 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10699f [0x0F, 0xB7, 0x43, 0x02] (LoadPre 0x10699f (fun s => AddrMode.addr (.base 3 (.d8 0x2)) s (0x10699f + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10699f 4 0 (.base 3 (.d8 0x2)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10699f 4 0 (.base 3 (.d8 0x2))).toInstrSpec (movzx_r32_m16_effect_step 0x10699f 0 (.base 3 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1069a3 [0x66, 0x31, 0x44, 0x24, 0x0A] (StorePre 0x1069a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x1069a3 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069a3 5 16 0 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x1069a3 5 0 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (xor_m16_r16_effect_step 0x1069a3 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1069a8 [0x0F, 0xB7, 0x43, 0x04] (LoadPre 0x1069a8 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1069a8 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1069a8 4 0 (.base 3 (.d8 0x4)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1069a8 4 0 (.base 3 (.d8 0x4))).toInstrSpec (movzx_r32_m16_effect_step 0x1069a8 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1069ac [0x66, 0x31, 0x44, 0x24, 0x0C] (StorePre 0x1069ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1069ac + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069ac 5 16 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x1069ac 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (xor_m16_r16_effect_step 0x1069ac 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1069b1 [0x0F, 0xB7, 0x43, 0x06] (LoadPre 0x1069b1 (fun s => AddrMode.addr (.base 3 (.d8 0x6)) s (0x1069b1 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1069b1 4 0 (.base 3 (.d8 0x6)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1069b1 4 0 (.base 3 (.d8 0x6))).toInstrSpec (movzx_r32_m16_effect_step 0x1069b1 0 (.base 3 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1069b5 [0x66, 0x31, 0x44, 0x24, 0x0E] (StorePre 0x1069b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1069b5 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069b5 5 16 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x1069b5 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (xor_m16_r16_effect_step 0x1069b5 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1069ba [0x0F, 0xB7, 0x43, 0x08] (LoadPre 0x1069ba (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1069ba + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1069ba 4 0 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1069ba 4 0 (.base 3 (.d8 0x8))).toInstrSpec (movzx_r32_m16_effect_step 0x1069ba 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1069be [0x66, 0x31, 0x44, 0x24, 0x10] (StorePre 0x1069be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1069be + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069be 5 16 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x1069be 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (xor_m16_r16_effect_step 0x1069be 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1069c3 [0x0F, 0xB7, 0x43, 0x0A] (LoadPre 0x1069c3 (fun s => AddrMode.addr (.base 3 (.d8 0xa)) s (0x1069c3 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1069c3 4 0 (.base 3 (.d8 0xa)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1069c3 4 0 (.base 3 (.d8 0xa))).toInstrSpec (movzx_r32_m16_effect_step 0x1069c3 0 (.base 3 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1069c7 [0x66, 0x31, 0x44, 0x24, 0x12] (StorePre 0x1069c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x1069c7 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069c7 5 16 0 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x1069c7 5 0 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (xor_m16_r16_effect_step 0x1069c7 0 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1069cc [0x48, 0x89, 0x5C, 0x24, 0x30] (StorePre 0x1069cc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1069cc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1069cc 3 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1069cc 3 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x1069cc 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x1069d1 [0x0F, 0xB7, 0x43, 0x0C] (LoadPre 0x1069d1 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x1069d1 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1069d1 4 0 (.base 3 (.d8 0xc)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1069d1 4 0 (.base 3 (.d8 0xc))).toInstrSpec (movzx_r32_m16_effect_step 0x1069d1 0 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1069d5 [0x66, 0x31, 0x44, 0x24, 0x14] (StorePre 0x1069d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1069d5 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069d5 5 16 0 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x1069d5 5 0 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (xor_m16_r16_effect_step 0x1069d5 0 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1069da [0x41, 0xBC, 0x07, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1069da) (movR32Imm32Effect 0x1069da 6 12 0x7)
      [] [] [.reg 12, .rip] :=
    (movR32Imm32Effect_footprint 0x1069da 6 12 0x7).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1069da 0x41 0xbc (by decide) (by decide) 0x7) pre_rip
  have f16 : InstrSpec 0x1069e0 [0x0F, 0xB7, 0x44, 0x24, 0x16] (LoadPre 0x1069e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x1069e0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1069e0 5 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1069e0 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m16_effect_step 0x1069e0 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1069e5 [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1069e5) (fun _ => nopEffect 0x1069e5 11)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1069e5 11).toInstrSpec (nop_m_effect_step 0x1069e5 [0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10699a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10699f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069a3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069a8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069ac) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069b1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069b5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069ba) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069be) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069c3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069c7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069cc) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069d1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069d5) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069da) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (12, 75), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069e0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (3, 3), (4, 4), (5, 5), (12, 75), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069e5) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (3, 3), (4, 4), (5, 5), (12, 75), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069f0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 80) (by decide) rfl

theorem block_l106997 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106997 :=
  Rest.liftedBlock (rest_l106997 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106997 x hx)

theorem rest_l1069f0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1069f0 bytes_l1069f0) (entryMap (live .l1069f0))
      7 0x1069f0 bytes_l1069f0 b_l1069f0 := by
  have f0 : InstrSpec 0x1069f0 [0x48, 0x8B, 0x5C, 0x24, 0x30] (LoadPre 0x1069f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1069f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1069f0 3 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1069f0 3 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x1069f0 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1069f5 [0x66, 0x42, 0x33, 0x04, 0x63] (LoadPre 0x1069f5 (fun s => AddrMode.addr (.sib 3 (some 12) 1 .none) s (0x1069f5 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x1069f5 5 0 (.sib 3 (some 12) 1 .none))
      [.gpr 0, .gpr 3, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1069f5 5 0 (.sib 3 (some 12) 1 .none)).toInstrSpec (xor_r16_m16_rex_effect_step 0x1069f5 0x42 (by decide) 0 (.sib 3 (some 12) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1069fa [0x66, 0x89, 0x44, 0x24, 0x16] (StorePre 0x1069fa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x1069fa + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1069fa 5 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1069fa 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m16_r16_effect_step 0x1069fa 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1069ff [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1069ff) (movR32Imm32Effect 0x1069ff 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1069ff 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x1069ff 0xbe (by decide) 0x8) pre_rip
  have f4 : InstrSpec 0x106a04 [0x4C, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x106a04) (leaR64Effect 0x106a04 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x106a04 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106a04 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x106a09 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x106a09) (movR64R64Effect 0x106a09 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106a09 7 14).toInstrSpec (mov_r64_r64_effect_step 0x106a09 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x106a0c [0xE8, 0xFF, 0xA0, 0xFF, 0xFF] (PushPre 0x106a0c 5) (callEffect (fun _ => 0x100b10) 0x106a11)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106a0c 0x100b10 0x106a11).toInstrSpec (call_rel32_effect_step 0x106a0c 0xffffa0ff (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069f5) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069fa) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1069ff) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (6, 58), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a04) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (6, 58), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a09) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (6, 58), (7, 62), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a0c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (3, 53), (4, 64), (5, 5), (6, 58), (7, 62), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l1069f0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1069f0 :=
  Rest.liftedBlock (rest_l1069f0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1069f0 x hx)

theorem rest_l106a11 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a11 bytes_l106a11) (entryMap (live .l106a11))
      2 0x106a11 bytes_l106a11 b_l106a11 := by
  have f0 : InstrSpec 0x106a11 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x106a11) (movR64R64Effect 0x106a11 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106a11 7 14).toInstrSpec (mov_r64_r64_effect_step 0x106a11 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106a14 [0xE8, 0xE7, 0x95, 0xFF, 0xFF] (PushPre 0x106a14 5) (callEffect (fun _ => 0x100000) 0x106a19)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106a14 0x100000 0x106a19).toInstrSpec (call_rel32_effect_step 0x106a14 0xffff95e7 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a14) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100000) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l106a11 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a11 :=
  Rest.liftedBlock (rest_l106a11 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a11 x hx)

theorem rest_l106a19_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x106a19 bytes_l106a19) [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x106a8a bytes_l106a19_1 b_l106a19_1 := by
  have f20 : InstrSpec 0x106a8a [0x66, 0x89, 0x4C, 0x24, 0x14] (StorePre 0x106a8a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106a8a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106a8a 5 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106a8a 5 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m16_r16_effect_step 0x106a8a 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x106a8f [0x0F, 0xB7, 0x44, 0x24, 0x16] (LoadPre 0x106a8f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106a8f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106a8f 5 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106a8f 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m16_effect_step 0x106a8f 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x106a94 [0x66, 0x42, 0x33, 0x44, 0x63, 0x10] (LoadPre 0x106a94 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x10)) s (0x106a94 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a94 6 0 (.sib 3 (some 12) 1 (.d8 0x10)))
      [.gpr 0, .gpr 3, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106a94 6 0 (.sib 3 (some 12) 1 (.d8 0x10))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106a94 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x106a9a [0x66, 0x89, 0x44, 0x24, 0x16] (StorePre 0x106a9a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106a9a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106a9a 5 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106a9a 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m16_r16_effect_step 0x106a9a 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x106a9f [0x49, 0x83, 0xFC, 0x67] (fun s => s.RIP = 0x106a9f) (cmpR64Imm8Effect 0x106a9f 12 0x67)
      [.gpr 12] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x106a9f 12 0x67).toInstrSpec (cmp_r64_imm8_effect_step 0x106a9f 0x49 0xfc 0x67 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a8f) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a94) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a9a) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a9f) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106aa3) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 95) (jcc_rel32_effect_step 0x106aa3 4 0x413) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l106a19 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106a19 bytes_l106a19) (entryMap (live .l106a19))
      26 0x106a19 bytes_l106a19 b_l106a19 := by
  have f0 : InstrSpec 0x106a19 [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x08] (LoadPre 0x106a19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106a19 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106a19 6 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x106a19 6 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106a19 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106a1f [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x0A] (LoadPre 0x106a1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106a1f + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106a1f 6 9 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x106a1f 6 9 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106a1f 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106a25 [0x66, 0x46, 0x33, 0x54, 0x63, 0x02] (LoadPre 0x106a25 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2)) s (0x106a25 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a25 6 10 (.sib 3 (some 12) 1 (.d8 0x2)))
      [.gpr 10, .gpr 3, .gpr 12] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106a25 6 10 (.sib 3 (some 12) 1 (.d8 0x2))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106a25 0x46 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106a2b [0x66, 0x44, 0x89, 0x54, 0x24, 0x08] (StorePre 0x106a2b 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106a2b + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106a2b 6 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106a2b 6 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106a2b 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106a31 [0x66, 0x46, 0x33, 0x4C, 0x63, 0x04] (LoadPre 0x106a31 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x4)) s (0x106a31 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a31 6 9 (.sib 3 (some 12) 1 (.d8 0x4)))
      [.gpr 9, .gpr 3, .gpr 12] [] [.reg 9, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106a31 6 9 (.sib 3 (some 12) 1 (.d8 0x4))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106a31 0x46 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x106a37 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x0A] (StorePre 0x106a37 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106a37 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106a37 6 9 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106a37 6 9 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106a37 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x106a3d [0x44, 0x0F, 0xB7, 0x44, 0x24, 0x0C] (LoadPre 0x106a3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106a3d + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106a3d 6 8 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x106a3d 6 8 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106a3d 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x106a43 [0x66, 0x46, 0x33, 0x44, 0x63, 0x06] (LoadPre 0x106a43 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x6)) s (0x106a43 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a43 6 8 (.sib 3 (some 12) 1 (.d8 0x6)))
      [.gpr 8, .gpr 3, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106a43 6 8 (.sib 3 (some 12) 1 (.d8 0x6))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106a43 0x46 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x106a49 [0x66, 0x44, 0x89, 0x44, 0x24, 0x0C] (StorePre 0x106a49 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106a49 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106a49 6 8 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106a49 6 8 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106a49 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x106a4f [0x0F, 0xB7, 0x7C, 0x24, 0x0E] (LoadPre 0x106a4f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106a4f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106a4f 5 7 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x106a4f 5 7 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m16_effect_step 0x106a4f 7 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x106a54 [0x66, 0x42, 0x33, 0x7C, 0x63, 0x08] (LoadPre 0x106a54 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x8)) s (0x106a54 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a54 6 7 (.sib 3 (some 12) 1 (.d8 0x8)))
      [.gpr 7, .gpr 3, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106a54 6 7 (.sib 3 (some 12) 1 (.d8 0x8))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106a54 0x42 (by decide) 7 (.sib 3 (some 12) 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x106a5a [0x66, 0x89, 0x7C, 0x24, 0x0E] (StorePre 0x106a5a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106a5a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106a5a 5 7 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106a5a 5 7 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x106a5a 7 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x106a5f [0x0F, 0xB7, 0x74, 0x24, 0x10] (LoadPre 0x106a5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106a5f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106a5f 5 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x106a5f 5 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (movzx_r32_m16_effect_step 0x106a5f 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x106a64 [0x66, 0x42, 0x33, 0x74, 0x63, 0x0A] (LoadPre 0x106a64 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0xa)) s (0x106a64 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a64 6 6 (.sib 3 (some 12) 1 (.d8 0xa)))
      [.gpr 6, .gpr 3, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106a64 6 6 (.sib 3 (some 12) 1 (.d8 0xa))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106a64 0x42 (by decide) 6 (.sib 3 (some 12) 1 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x106a6a [0x66, 0x89, 0x74, 0x24, 0x10] (StorePre 0x106a6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106a6a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106a6a 5 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106a6a 5 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m16_r16_effect_step 0x106a6a 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x106a6f [0x0F, 0xB7, 0x54, 0x24, 0x12] (LoadPre 0x106a6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106a6f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106a6f 5 2 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x106a6f 5 2 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (movzx_r32_m16_effect_step 0x106a6f 2 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x106a74 [0x66, 0x42, 0x33, 0x54, 0x63, 0x0C] (LoadPre 0x106a74 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0xc)) s (0x106a74 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a74 6 2 (.sib 3 (some 12) 1 (.d8 0xc)))
      [.gpr 2, .gpr 3, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106a74 6 2 (.sib 3 (some 12) 1 (.d8 0xc))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106a74 0x42 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x106a7a [0x66, 0x89, 0x54, 0x24, 0x12] (StorePre 0x106a7a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106a7a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106a7a 5 2 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106a7a 5 2 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (mov_m16_r16_effect_step 0x106a7a 2 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x106a7f [0x0F, 0xB7, 0x4C, 0x24, 0x14] (LoadPre 0x106a7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106a7f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106a7f 5 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x106a7f 5 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m16_effect_step 0x106a7f 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x106a84 [0x66, 0x42, 0x33, 0x4C, 0x63, 0x0E] (LoadPre 0x106a84 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0xe)) s (0x106a84 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a84 6 1 (.sib 3 (some 12) 1 (.d8 0xe)))
      [.gpr 1, .gpr 3, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106a84 6 1 (.sib 3 (some 12) 1 (.d8 0xe))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106a84 0x42 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a1f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a25) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a2b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a31) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a37) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a3d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 63), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a43) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a49) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a4f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 68), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a54) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a5a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a5f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 73), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a64) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a6a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a6f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(2, 78), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a74) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a7a) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a7f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 83), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a84) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106a8a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106a19_1 code

theorem block_l106a19 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106a19 :=
  Rest.liftedBlock (rest_l106a19 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106a19 x hx)

theorem rest_l106aa9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106aa9 bytes_l106aa9) (entryMap (live .l106aa9))
      3 0x106aa9 bytes_l106aa9 b_l106aa9 := by
  have f0 : InstrSpec 0x106aa9 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106aa9) (movR32Imm32Effect 0x106aa9 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x106aa9 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x106aa9 0xbe (by decide) 0x8) pre_rip
  have f1 : InstrSpec 0x106aae [0x48, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x106aae) (leaR64Effect 0x106aae 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x106aae 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106aae 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106ab3 [0xE8, 0x58, 0xA0, 0xFF, 0xFF] (PushPre 0x106ab3 5) (callEffect (fun _ => 0x100b10) 0x106ab8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106ab3 0x100b10 0x106ab8).toInstrSpec (call_rel32_effect_step 0x106ab3 0xffffa058 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106aae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ab3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l106aa9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106aa9 :=
  Rest.liftedBlock (rest_l106aa9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106aa9 x hx)

theorem rest_l106ab8_6 [Bindings] (code : CodeMap) :
    Rest (n := 283) code lifted (codeRange 0x106ab8 bytes_l106ab8) [(0, 181), (1, 280), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x106c9d bytes_l106ab8_6 b_l106ab8_6 := by
  have f120 : InstrSpec 0x106c9d [0x8B, 0x54, 0x24, 0x24] (LoadPre 0x106c9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106c9d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c9d 2 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x106c9d 2 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_r32_m32_low_effect_step 0x106c9d 2 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f121 : InstrSpec 0x106ca1 [0x44, 0x31, 0xDA] (fun s => s.RIP = 0x106ca1) (xorR32R32Effect 0x106ca1 3 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106ca1 3 2 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x106ca1 0x44 0xda (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x106ca4 [0x44, 0x31, 0xDE] (fun s => s.RIP = 0x106ca4) (xorR32R32Effect 0x106ca4 3 6 11)
      [.gpr 6, .gpr 11] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106ca4 3 6 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x106ca4 0x44 0xde (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x106ca7 [0x89, 0xD1] (fun s => s.RIP = 0x106ca7) (movR32R32Effect 0x106ca7 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106ca7 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x106ca7 0xd1 (by decide)) pre_rip
  have f124 : InstrSpec 0x106ca9 [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x106ca9) (rolR16Effect 0x106ca9 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x106ca9 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x106ca9 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x106cad [0x66, 0x42, 0x33, 0x4C, 0x63, 0x1E] (LoadPre 0x106cad (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1e)) s (0x106cad + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106cad 6 1 (.sib 3 (some 12) 1 (.d8 0x1e)))
      [.gpr 1, .gpr 3, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106cad 6 1 (.sib 3 (some 12) 1 (.d8 0x1e))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106cad 0x42 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f126 : InstrSpec 0x106cb3 [0x31, 0xCE] (fun s => s.RIP = 0x106cb3) (xorR32R32Effect 0x106cb3 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106cb3 2 6 1).toInstrSpec (xor_r32_r32_effect_step 0x106cb3 0xce (by decide)) pre_rip
  have f127 : InstrSpec 0x106cb5 [0x66, 0x89, 0x74, 0x24, 0x14] (StorePre 0x106cb5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106cb5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106cb5 5 6 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106cb5 5 6 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m16_r16_effect_step 0x106cb5 6 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f128 : InstrSpec 0x106cba [0x89, 0xD1] (fun s => s.RIP = 0x106cba) (movR32R32Effect 0x106cba 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106cba 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x106cba 0xd1 (by decide)) pre_rip
  have f129 : InstrSpec 0x106cbc [0x31, 0xC1] (fun s => s.RIP = 0x106cbc) (xorR32R32Effect 0x106cbc 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106cbc 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106cbc 0xc1 (by decide)) pre_rip
  have f130 : InstrSpec 0x106cbe [0x66, 0x41, 0xC1, 0xC6, 0x08] (fun s => s.RIP = 0x106cbe) (rolR16Effect 0x106cbe 5 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR16Effect_footprint 0x106cbe 5 14 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106cbe 0x41 0xc6 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x106cc3 [0x66, 0x46, 0x33, 0x74, 0x63, 0x20] (LoadPre 0x106cc3 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x20)) s (0x106cc3 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106cc3 6 14 (.sib 3 (some 12) 1 (.d8 0x20)))
      [.gpr 14, .gpr 3, .gpr 12] [] [.reg 14, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106cc3 6 14 (.sib 3 (some 12) 1 (.d8 0x20))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106cc3 0x46 (by decide) 6 (.sib 3 (some 12) 1 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f132 : InstrSpec 0x106cc9 [0x44, 0x31, 0xF1] (fun s => s.RIP = 0x106cc9) (xorR32R32Effect 0x106cc9 3 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106cc9 3 1 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x106cc9 0x44 0xf1 (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x106ccc [0x66, 0x89, 0x4C, 0x24, 0x16] (StorePre 0x106ccc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106ccc + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106ccc 5 1 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106ccc 5 1 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m16_r16_effect_step 0x106ccc 1 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f134 : InstrSpec 0x106cd1 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106cd1) (movR32Imm32Effect 0x106cd1 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x106cd1 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x106cd1 0xbe (by decide) 0x8) pre_rip
  have f135 : InstrSpec 0x106cd6 [0x4C, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x106cd6) (leaR64Effect 0x106cd6 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (leaR64Effect_footprint 0x106cd6 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106cd6 0x4c (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x106cdb [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x106cdb) (movR64R64Effect 0x106cdb 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106cdb 7 14).toInstrSpec (mov_r64_r64_effect_step 0x106cdb 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x106cde [0xE8, 0x2D, 0x9E, 0xFF, 0xFF] (PushPre 0x106cde 5) (callEffect (fun _ => 0x100b10) 0x106ce3)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106cde 0x100b10 0x106ce3).toInstrSpec (call_rel32_effect_step 0x106cde 0xffff9e2d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f120 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 181), (1, 280), (2, 283), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ca1) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 285) (RestInside.out (n := 285) f121 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 286) (ρ' := [(0, 181), (1, 280), (2, 285), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ca4) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f122 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 181), (1, 280), (2, 285), (3, 191), (4, 4), (5, 197), (6, 287), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ca7) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f123 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 181), (1, 289), (2, 285), (3, 191), (4, 4), (5, 197), (6, 287), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ca9) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f124 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 181), (1, 291), (2, 285), (3, 191), (4, 4), (5, 197), (6, 287), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cad) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f125 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 181), (1, 293), (2, 285), (3, 191), (4, 4), (5, 197), (6, 287), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cb3) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f126 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 181), (1, 293), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cb5) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.exec (n := 297) (ρ' := [(0, 181), (1, 293), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cba) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f128 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 181), (1, 298), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cbc) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f129 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 181), (1, 300), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cbe) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f130 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 181), (1, 300), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 302), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cc3) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f131 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 181), (1, 300), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 304), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cc9) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f132 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 304), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ccc) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.exec (n := 308) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 304), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cd1) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f134 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 4), (5, 197), (6, 309), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 304), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cd6) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f135 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 312) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 4), (5, 197), (6, 309), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 311), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cdb) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f136 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 314) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 4), (5, 197), (6, 309), (7, 313), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 311), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cde) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 315) (RestInside.out (n := 315) f137 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 316) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 315), (5, 197), (6, 309), (7, 313), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 311), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f137 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 317) (by decide) (by decide) rfl rfl

theorem rest_l106ab8_5 [Bindings] (code : CodeMap) :
    Rest (n := 246) code lifted (codeRange 0x106ab8 bytes_l106ab8) [(0, 181), (1, 244), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]
      38 0x106c55 bytes_l106ab8_5 b_l106ab8_5 := by
  have f100 : InstrSpec 0x106c55 [0x66, 0x89, 0x7C, 0x24, 0x0E] (StorePre 0x106c55 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106c55 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106c55 5 7 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106c55 5 7 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x106c55 7 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f101 : InstrSpec 0x106c5a [0x89, 0xCA] (fun s => s.RIP = 0x106c5a) (movR32R32Effect 0x106c5a 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x106c5a 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x106c5a 0xca (by decide)) pre_rip
  have f102 : InstrSpec 0x106c5c [0x89, 0xCF] (fun s => s.RIP = 0x106c5c) (movR32R32Effect 0x106c5c 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x106c5c 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x106c5c 0xcf (by decide)) pre_rip
  have f103 : InstrSpec 0x106c5e [0x66, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x106c5e) (rolR16Effect 0x106c5e 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR16Effect_footprint 0x106c5e 4 2 8).toInstrSpec (rol_r16_imm8_effect_step 0x106c5e 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x106c62 [0x45, 0x31, 0xEF] (fun s => s.RIP = 0x106c62) (xorR32R32Effect 0x106c62 3 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c62 3 15 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c62 0x45 0xef (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x106c65 [0x66, 0x42, 0x33, 0x54, 0x63, 0x1A] (LoadPre 0x106c65 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1a)) s (0x106c65 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106c65 6 2 (.sib 3 (some 12) 1 (.d8 0x1a)))
      [.gpr 2, .gpr 3, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106c65 6 2 (.sib 3 (some 12) 1 (.d8 0x1a))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106c65 0x42 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f106 : InstrSpec 0x106c6b [0x45, 0x31, 0xF7] (fun s => s.RIP = 0x106c6b) (xorR32R32Effect 0x106c6b 3 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c6b 3 15 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c6b 0x45 0xf7 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x106c6e [0x41, 0x31, 0xD7] (fun s => s.RIP = 0x106c6e) (xorR32R32Effect 0x106c6e 3 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c6e 3 15 2).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c6e 0x41 0xd7 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x106c71 [0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x106c71 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106c71 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c71 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x106c71 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x106c71 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f109 : InstrSpec 0x106c75 [0x44, 0x8B, 0x44, 0x24, 0x1C] (LoadPre 0x106c75 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x106c75 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x106c75 8 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x106c75 8 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_effect_step 0x106c75 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f110 : InstrSpec 0x106c7a [0x44, 0x31, 0xC1] (fun s => s.RIP = 0x106c7a) (xorR32R32Effect 0x106c7a 3 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c7a 3 1 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c7a 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x106c7d [0x66, 0x44, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x106c7d 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106c7d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106c7d 6 15 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106c7d 6 15 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106c7d 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f112 : InstrSpec 0x106c83 [0x89, 0xCA] (fun s => s.RIP = 0x106c83) (movR32R32Effect 0x106c83 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x106c83 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x106c83 0xca (by decide)) pre_rip
  have f113 : InstrSpec 0x106c85 [0x89, 0xCE] (fun s => s.RIP = 0x106c85) (movR32R32Effect 0x106c85 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x106c85 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x106c85 0xce (by decide)) pre_rip
  have f114 : InstrSpec 0x106c87 [0x66, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x106c87) (rolR16Effect 0x106c87 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR16Effect_footprint 0x106c87 4 2 8).toInstrSpec (rol_r16_imm8_effect_step 0x106c87 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x106c8b [0x66, 0x42, 0x33, 0x54, 0x63, 0x1C] (LoadPre 0x106c8b (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1c)) s (0x106c8b + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106c8b 6 2 (.sib 3 (some 12) 1 (.d8 0x1c)))
      [.gpr 2, .gpr 3, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106c8b 6 2 (.sib 3 (some 12) 1 (.d8 0x1c))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106c8b 0x42 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f116 : InstrSpec 0x106c91 [0x89, 0xF9] (fun s => s.RIP = 0x106c91) (movR32R32Effect 0x106c91 2 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106c91 2 1 7).toInstrSpec (mov_r32_r32_effect_step 0x106c91 0xf9 (by decide)) pre_rip
  have f117 : InstrSpec 0x106c93 [0x44, 0x31, 0xC1] (fun s => s.RIP = 0x106c93) (xorR32R32Effect 0x106c93 3 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c93 3 1 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c93 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x106c96 [0x31, 0xD1] (fun s => s.RIP = 0x106c96) (xorR32R32Effect 0x106c96 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c96 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x106c96 0xd1 (by decide)) pre_rip
  have f119 : InstrSpec 0x106c98 [0x66, 0x89, 0x4C, 0x24, 0x12] (StorePre 0x106c98 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106c98 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106c98 5 1 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106c98 5 1 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (mov_m16_r16_effect_step 0x106c98 1 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 246) (RestInside.exec (n := 246) (ρ' := [(0, 181), (1, 244), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c5a) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f101 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 181), (1, 244), (2, 247), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c5c) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f102 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 181), (1, 244), (2, 247), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c5e) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f103 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 181), (1, 244), (2, 251), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c62) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f104 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 181), (1, 244), (2, 251), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 253), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c65) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f105 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 181), (1, 244), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 253), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c6b) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f106 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 181), (1, 244), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 257), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c6e) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f107 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 181), (1, 244), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c71) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f108 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 181), (1, 261), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c75) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f109 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 181), (1, 261), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c7a) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f110 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 181), (1, 265), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c7d) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.exec (n := 267) (ρ' := [(0, 181), (1, 265), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c83) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f112 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 181), (1, 265), (2, 268), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c85) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f113 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 181), (1, 265), (2, 268), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c87) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f114 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 181), (1, 265), (2, 272), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c8b) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f115 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 181), (1, 265), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c91) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f116 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 181), (1, 276), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c93) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f117 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 181), (1, 278), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c96) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f118 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 181), (1, 280), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c98) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.exec (n := 282) (ρ' := [(0, 181), (1, 280), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c9d) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l106ab8_6 code

theorem rest_l106ab8_4 [Bindings] (code : CodeMap) :
    Rest (n := 208) code lifted (codeRange 0x106ab8 bytes_l106ab8) [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 206), (9, 202), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      58 0x106c0b bytes_l106ab8_4 b_l106ab8_4 := by
  have f80 : InstrSpec 0x106c0b [0x66, 0x46, 0x33, 0x44, 0x63, 0x14] (LoadPre 0x106c0b (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x14)) s (0x106c0b + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106c0b 6 8 (.sib 3 (some 12) 1 (.d8 0x14)))
      [.gpr 8, .gpr 3, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106c0b 6 8 (.sib 3 (some 12) 1 (.d8 0x14))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106c0b 0x46 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f81 : InstrSpec 0x106c11 [0x45, 0x31, 0xF1] (fun s => s.RIP = 0x106c11) (xorR32R32Effect 0x106c11 3 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c11 3 9 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c11 0x45 0xf1 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x106c14 [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x106c14) (xorR32R32Effect 0x106c14 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c14 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c14 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x106c17 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x0A] (StorePre 0x106c17 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106c17 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106c17 6 9 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106c17 6 9 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106c17 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f84 : InstrSpec 0x106c1d [0x31, 0xCF] (fun s => s.RIP = 0x106c1d) (xorR32R32Effect 0x106c1d 2 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c1d 2 7 1).toInstrSpec (xor_r32_r32_effect_step 0x106c1d 0xcf (by decide)) pre_rip
  have f85 : InstrSpec 0x106c1f [0x31, 0xCA] (fun s => s.RIP = 0x106c1f) (xorR32R32Effect 0x106c1f 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c1f 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x106c1f 0xca (by decide)) pre_rip
  have f86 : InstrSpec 0x106c21 [0x41, 0x89, 0xF8] (fun s => s.RIP = 0x106c21) (movR32R32Effect 0x106c21 3 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x106c21 3 8 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x106c21 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x106c24 [0x66, 0x41, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x106c24) (rolR16Effect 0x106c24 5 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR16Effect_footprint 0x106c24 5 8 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106c24 0x41 0xc0 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x106c29 [0x66, 0x46, 0x33, 0x44, 0x63, 0x16] (LoadPre 0x106c29 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x16)) s (0x106c29 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106c29 6 8 (.sib 3 (some 12) 1 (.d8 0x16)))
      [.gpr 8, .gpr 3, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106c29 6 8 (.sib 3 (some 12) 1 (.d8 0x16))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106c29 0x46 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f89 : InstrSpec 0x106c2f [0x44, 0x31, 0xC2] (fun s => s.RIP = 0x106c2f) (xorR32R32Effect 0x106c2f 3 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c2f 3 2 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c2f 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x106c32 [0x41, 0x31, 0xF7] (fun s => s.RIP = 0x106c32) (xorR32R32Effect 0x106c32 3 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c32 3 15 6).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c32 0x41 0xf7 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x106c35 [0x66, 0x89, 0x54, 0x24, 0x0C] (StorePre 0x106c35 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106c35 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106c35 5 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106c35 5 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x106c35 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f92 : InstrSpec 0x106c3a [0x44, 0x89, 0xFA] (fun s => s.RIP = 0x106c3a) (movR32R32Effect 0x106c3a 3 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x106c3a 3 2 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x106c3a 0x44 0xfa (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x106c3d [0x66, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x106c3d) (rolR16Effect 0x106c3d 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR16Effect_footprint 0x106c3d 4 2 8).toInstrSpec (rol_r16_imm8_effect_step 0x106c3d 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x106c41 [0x66, 0x42, 0x33, 0x54, 0x63, 0x18] (LoadPre 0x106c41 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x18)) s (0x106c41 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106c41 6 2 (.sib 3 (some 12) 1 (.d8 0x18)))
      [.gpr 2, .gpr 3, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106c41 6 2 (.sib 3 (some 12) 1 (.d8 0x18))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106c41 0x42 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f95 : InstrSpec 0x106c47 [0x31, 0xF7] (fun s => s.RIP = 0x106c47) (xorR32R32Effect 0x106c47 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c47 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x106c47 0xf7 (by decide)) pre_rip
  have f96 : InstrSpec 0x106c49 [0x44, 0x31, 0xF7] (fun s => s.RIP = 0x106c49) (xorR32R32Effect 0x106c49 3 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c49 3 7 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c49 0x44 0xf7 (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x106c4c [0x31, 0xD7] (fun s => s.RIP = 0x106c4c) (xorR32R32Effect 0x106c4c 2 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c4c 2 7 2).toInstrSpec (xor_r32_r32_effect_step 0x106c4c 0xd7 (by decide)) pre_rip
  have f98 : InstrSpec 0x106c4e [0x8B, 0x4C, 0x24, 0x28] (LoadPre 0x106c4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106c4e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c4e 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x106c4e 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x106c4e 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f99 : InstrSpec 0x106c52 [0x44, 0x31, 0xE9] (fun s => s.RIP = 0x106c52) (xorR32R32Effect 0x106c52 3 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c52 3 1 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c52 0x44 0xe9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f80 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 208), (9, 202), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c11) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f81 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 208), (9, 210), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c14) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f82 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 208), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c17) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.exec (n := 214) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 208), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c1d) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f84 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 208), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c1f) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f85 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 181), (1, 107), (2, 217), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 208), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c21) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f86 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 181), (1, 107), (2, 217), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 219), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c24) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f87 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 181), (1, 107), (2, 217), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 221), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c29) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f88 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 181), (1, 107), (2, 217), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c2f) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f89 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 181), (1, 107), (2, 225), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c32) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f90 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 181), (1, 107), (2, 225), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c35) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.exec (n := 229) (ρ' := [(0, 181), (1, 107), (2, 225), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c3a) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f92 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(0, 181), (1, 107), (2, 230), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c3d) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f93 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 181), (1, 107), (2, 232), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c41) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f94 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 181), (1, 107), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c47) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f95 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 181), (1, 107), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 236), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c49) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f96 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 181), (1, 107), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 238), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c4c) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f97 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 181), (1, 107), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c4e) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f98 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 181), (1, 242), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c52) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f99 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 181), (1, 244), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c55) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106ab8_5 code

theorem rest_l106ab8_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x106ab8 bytes_l106ab8) [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 161), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      78 0x106bbb bytes_l106ab8_3 b_l106ab8_3 := by
  have f60 : InstrSpec 0x106bbb [0x45, 0x89, 0xF2] (fun s => s.RIP = 0x106bbb) (movR32R32Effect 0x106bbb 3 10 14)
      [.gpr 14] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x106bbb 3 10 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x106bbb 0x45 0xf2 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x106bbe [0x66, 0x41, 0xC1, 0xC2, 0x0A] (fun s => s.RIP = 0x106bbe) (rolR16Effect 0x106bbe 5 10 10)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x106bbe 5 10 10).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106bbe 0x41 0xc2 0xa (by decide) (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x106bc3 [0x41, 0x81, 0xE2, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x106bc3) (andR32Imm32Effect 0x106bc3 7 10 0x3333)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106bc3 7 10 0x3333).toInstrSpec (and_r32_imm32_rex_effect_step 0x106bc3 0x41 0xe2 0x3333 (by decide) (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x106bca [0x44, 0x89, 0xF0] (fun s => s.RIP = 0x106bca) (movR32R32Effect 0x106bca 3 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106bca 3 0 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x106bca 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x106bcd [0x66, 0xC1, 0xC0, 0x0E] (fun s => s.RIP = 0x106bcd) (rolR16Effect 0x106bcd 4 0 14)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x106bcd 4 0 14).toInstrSpec (rol_r16_imm8_effect_step 0x106bcd 0xc0 0xe (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x106bd1 [0x25, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x106bd1) (andEaxImm32Effect 0x106bd1 0xffffcccc)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106bd1 0xffffcccc).toInstrSpec (and_eax_imm32_effect_step 0x106bd1 0xffffcccc) pre_rip
  have f66 : InstrSpec 0x106bd6 [0x44, 0x09, 0xD0] (fun s => s.RIP = 0x106bd6) (orR32R32Effect 0x106bd6 3 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106bd6 3 0 10).toInstrSpec (or_r32_r32_rex_effect_step 0x106bd6 0x44 0xd0 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x106bd9 [0x41, 0x31, 0xE9] (fun s => s.RIP = 0x106bd9) (xorR32R32Effect 0x106bd9 3 9 5)
      [.gpr 9, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106bd9 3 9 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x106bd9 0x41 0xe9 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x106bdc [0x41, 0x31, 0xC6] (fun s => s.RIP = 0x106bdc) (xorR32R32Effect 0x106bdc 3 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106bdc 3 14 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x106bdc 0x41 0xc6 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x106bdf [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x106bdf) (movR32R32Effect 0x106bdf 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x106bdf 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x106bdf 0x45 0xca (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x106be2 [0x66, 0x41, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x106be2) (rolR16Effect 0x106be2 5 10 8)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x106be2 5 10 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106be2 0x41 0xc2 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x106be7 [0x48, 0x8B, 0x5C, 0x24, 0x30] (LoadPre 0x106be7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106be7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106be7 3 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x106be7 3 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x106be7 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f72 : InstrSpec 0x106bec [0x66, 0x46, 0x33, 0x54, 0x63, 0x12] (LoadPre 0x106bec (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x12)) s (0x106bec + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106bec 6 10 (.sib 3 (some 12) 1 (.d8 0x12)))
      [.gpr 10, .gpr 3, .gpr 12] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106bec 6 10 (.sib 3 (some 12) 1 (.d8 0x12))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106bec 0x46 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f73 : InstrSpec 0x106bf2 [0x44, 0x31, 0xF5] (fun s => s.RIP = 0x106bf2) (xorR32R32Effect 0x106bf2 3 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106bf2 3 5 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x106bf2 0x44 0xf5 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x106bf5 [0x44, 0x31, 0xD5] (fun s => s.RIP = 0x106bf5) (xorR32R32Effect 0x106bf5 3 5 10)
      [.gpr 5, .gpr 10] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106bf5 3 5 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x106bf5 0x44 0xd5 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x106bf8 [0x66, 0x89, 0x6C, 0x24, 0x08] (StorePre 0x106bf8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106bf8 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106bf8 5 5 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106bf8 5 5 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m16_r16_effect_step 0x106bf8 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x106bfd [0x44, 0x31, 0xC2] (fun s => s.RIP = 0x106bfd) (xorR32R32Effect 0x106bfd 3 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106bfd 3 2 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x106bfd 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x106c00 [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x106c00) (xorR32R32Effect 0x106c00 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106c00 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x106c00 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x106c03 [0x41, 0x89, 0xD0] (fun s => s.RIP = 0x106c03) (movR32R32Effect 0x106c03 3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x106c03 3 8 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x106c03 0x41 0xd0 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x106c06 [0x66, 0x41, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x106c06) (rolR16Effect 0x106c06 5 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR16Effect_footprint 0x106c06 5 8 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106c06 0x41 0xc0 0x8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 169), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bbe) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f61 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 171), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bc3) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f62 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bca) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f63 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 175), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bcd) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 177), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bd1) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f65 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 179), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bd6) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f66 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bd9) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f67 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bdc) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f68 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 173), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bdf) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f69 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 187), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106be2) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f70 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 189), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106be7) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f71 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 191), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 189), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bec) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f72 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 191), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bf2) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f73 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 191), (4, 4), (5, 195), (6, 121), (7, 55), (8, 97), (9, 183), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bf5) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f74 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 97), (9, 183), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bf8) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.exec (n := 199) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 97), (9, 183), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bfd) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f76 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 97), (9, 183), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c00) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f77 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 97), (9, 202), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c03) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f78 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 204), (9, 202), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c06) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f79 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 206), (9, 202), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106c0b) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106ab8_4 code

theorem rest_l106ab8_2 [Bindings] (code : CodeMap) :
    Rest (n := 132) code lifted (codeRange 0x106ab8 bytes_l106ab8) [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 130), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      98 0x106b5e bytes_l106ab8_2 b_l106ab8_2 := by
  have f40 : InstrSpec 0x106b5e [0x41, 0x81, 0xE5, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x106b5e) (andR32Imm32Effect 0x106b5e 7 13 0xffffcccc)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106b5e 7 13 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x106b5e 0x41 0xe5 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x106b65 [0x41, 0x09, 0xC5] (fun s => s.RIP = 0x106b65) (orR32R32Effect 0x106b65 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106b65 3 13 0).toInstrSpec (or_r32_r32_rex_effect_step 0x106b65 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x106b68 [0x44, 0x89, 0x54, 0x24, 0x20] (StorePre 0x106b68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106b68 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106b68 10 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x106b68 10 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_effect_step 0x106b68 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x106b6d [0x44, 0x89, 0xD0] (fun s => s.RIP = 0x106b6d) (movR32R32Effect 0x106b6d 3 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106b6d 3 0 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x106b6d 0x44 0xd0 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x106b70 [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x106b70) (rolR16Effect 0x106b70 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b70 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x106b70 0xc0 0xa (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x106b74 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x106b74) (andEaxImm32Effect 0x106b74 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106b74 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x106b74 0x3333) pre_rip
  have f46 : InstrSpec 0x106b79 [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x106b79) (movR32R32Effect 0x106b79 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x106b79 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x106b79 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x106b7c [0x66, 0x41, 0xC1, 0xC3, 0x0E] (fun s => s.RIP = 0x106b7c) (rolR16Effect 0x106b7c 5 11 14)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b7c 5 11 14).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106b7c 0x41 0xc3 0xe (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x106b81 [0x41, 0x81, 0xE3, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x106b81) (andR32Imm32Effect 0x106b81 7 11 0xffffcccc)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106b81 7 11 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x106b81 0x41 0xe3 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x106b88 [0x89, 0x5C, 0x24, 0x24] (StorePre 0x106b88 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106b88 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x106b88 3 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106b88 3 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_m32_r32_low_effect_step 0x106b88 3 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x106b8c [0x41, 0x89, 0xDA] (fun s => s.RIP = 0x106b8c) (movR32R32Effect 0x106b8c 3 10 3)
      [.gpr 3] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x106b8c 3 10 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x106b8c 0x41 0xda (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x106b8f [0x66, 0x41, 0xC1, 0xC2, 0x0A] (fun s => s.RIP = 0x106b8f) (rolR16Effect 0x106b8f 5 10 10)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b8f 5 10 10).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106b8f 0x41 0xc2 0xa (by decide) (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x106b94 [0x41, 0x09, 0xC3] (fun s => s.RIP = 0x106b94) (orR32R32Effect 0x106b94 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106b94 3 11 0).toInstrSpec (or_r32_r32_rex_effect_step 0x106b94 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x106b97 [0x44, 0x89, 0x5C, 0x24, 0x1C] (StorePre 0x106b97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x106b97 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106b97 11 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x106b97 11 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m32_r32_effect_step 0x106b97 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x106b9c [0x41, 0x89, 0xDB] (fun s => s.RIP = 0x106b9c) (movR32R32Effect 0x106b9c 3 11 3)
      [.gpr 3] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x106b9c 3 11 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x106b9c 0x41 0xdb (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x106b9f [0x66, 0x41, 0xC1, 0xC3, 0x0E] (fun s => s.RIP = 0x106b9f) (rolR16Effect 0x106b9f 5 11 14)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b9f 5 11 14).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106b9f 0x41 0xc3 0xe (by decide) (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x106ba4 [0x41, 0x81, 0xE2, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x106ba4) (andR32Imm32Effect 0x106ba4 7 10 0x3333)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106ba4 7 10 0x3333).toInstrSpec (and_r32_imm32_rex_effect_step 0x106ba4 0x41 0xe2 0x3333 (by decide) (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x106bab [0x41, 0x81, 0xE3, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x106bab) (andR32Imm32Effect 0x106bab 7 11 0xffffcccc)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106bab 7 11 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x106bab 0x41 0xe3 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x106bb2 [0x45, 0x09, 0xD3] (fun s => s.RIP = 0x106bb2) (orR32R32Effect 0x106bb2 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106bb2 3 11 10).toInstrSpec (or_r32_r32_rex_effect_step 0x106bb2 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x106bb5 [0x44, 0x0F, 0xB7, 0x74, 0x24, 0x16] (LoadPre 0x106bb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106bb5 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106bb5 6 14 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M16Effect_footprint 0x106bb5 6 14 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106bb5 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f40 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 132), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b65) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f41 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b68) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b6d) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 137), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b70) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 139), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b74) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b79) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f46 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (11, 143), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b7c) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f47 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (11, 145), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b81) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f48 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (11, 147), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b88) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.exec (n := 149) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (11, 147), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b8c) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f50 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 150), (11, 147), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b8f) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f51 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 152), (11, 147), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b94) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 152), (11, 154), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b97) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.exec (n := 156) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 152), (11, 154), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b9c) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 152), (11, 157), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b9f) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 152), (11, 159), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ba4) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 161), (11, 159), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bab) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 161), (11, 163), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bb2) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 161), (11, 165), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bb5) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 161), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106bbb) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106ab8_3 code

theorem rest_l106ab8_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x106ab8 bytes_l106ab8) [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (8, 91), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      118 0x106b10 bytes_l106ab8_1 b_l106ab8_1 := by
  have f20 : InstrSpec 0x106b10 [0x89, 0xFE] (fun s => s.RIP = 0x106b10) (movR32R32Effect 0x106b10 2 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x106b10 2 6 7).toInstrSpec (mov_r32_r32_effect_step 0x106b10 0xfe (by decide)) pre_rip
  have f21 : InstrSpec 0x106b12 [0x66, 0xC1, 0xC6, 0x0A] (fun s => s.RIP = 0x106b12) (rolR16Effect 0x106b12 4 6 10)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b12 4 6 10).toInstrSpec (rol_r16_imm8_effect_step 0x106b12 0xc6 0xa (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x106b16 [0x41, 0x09, 0xC0] (fun s => s.RIP = 0x106b16) (orR32R32Effect 0x106b16 3 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106b16 3 8 0).toInstrSpec (or_r32_r32_rex_effect_step 0x106b16 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x106b19 [0x89, 0xF9] (fun s => s.RIP = 0x106b19) (movR32R32Effect 0x106b19 2 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106b19 2 1 7).toInstrSpec (mov_r32_r32_effect_step 0x106b19 0xf9 (by decide)) pre_rip
  have f24 : InstrSpec 0x106b1b [0x66, 0xC1, 0xC1, 0x0E] (fun s => s.RIP = 0x106b1b) (rolR16Effect 0x106b1b 4 1 14)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b1b 4 1 14).toInstrSpec (rol_r16_imm8_effect_step 0x106b1b 0xc1 0xe (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x106b1f [0x81, 0xE6, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x106b1f) (andR32Imm32Effect 0x106b1f 6 6 0x3333)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106b1f 6 6 0x3333).toInstrSpec (and_r32_imm32_effect_step 0x106b1f 0xe6 0x3333 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x106b25 [0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x106b25) (andR32Imm32Effect 0x106b25 6 1 0xffffcccc)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106b25 6 1 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x106b25 0xe1 0xffffcccc (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x106b2b [0x09, 0xF1] (fun s => s.RIP = 0x106b2b) (orR32R32Effect 0x106b2b 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106b2b 2 1 6).toInstrSpec (or_r32_r32_effect_step 0x106b2b 0xf1 (by decide)) pre_rip
  have f28 : InstrSpec 0x106b2d [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x106b2d) (movR32R32Effect 0x106b2d 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106b2d 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x106b2d 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x106b30 [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x106b30) (rolR16Effect 0x106b30 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b30 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x106b30 0xc0 0xa (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x106b34 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x106b34) (andEaxImm32Effect 0x106b34 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106b34 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x106b34 0x3333) pre_rip
  have f31 : InstrSpec 0x106b39 [0x44, 0x89, 0xFE] (fun s => s.RIP = 0x106b39) (movR32R32Effect 0x106b39 3 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x106b39 3 6 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x106b39 0x44 0xfe (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x106b3c [0x66, 0xC1, 0xC6, 0x0E] (fun s => s.RIP = 0x106b3c) (rolR16Effect 0x106b3c 4 6 14)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b3c 4 6 14).toInstrSpec (rol_r16_imm8_effect_step 0x106b3c 0xc6 0xe (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x106b40 [0x81, 0xE6, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x106b40) (andR32Imm32Effect 0x106b40 6 6 0xffffcccc)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106b40 6 6 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x106b40 0xe6 0xffffcccc (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x106b46 [0x09, 0xC6] (fun s => s.RIP = 0x106b46) (orR32R32Effect 0x106b46 2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106b46 2 6 0).toInstrSpec (or_r32_r32_effect_step 0x106b46 0xc6 (by decide)) pre_rip
  have f35 : InstrSpec 0x106b48 [0x44, 0x89, 0x6C, 0x24, 0x28] (StorePre 0x106b48 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106b48 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106b48 13 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x106b48 13 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m32_r32_effect_step 0x106b48 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x106b4d [0x44, 0x89, 0xE8] (fun s => s.RIP = 0x106b4d) (movR32R32Effect 0x106b4d 3 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106b4d 3 0 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x106b4d 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x106b50 [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x106b50) (rolR16Effect 0x106b50 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b50 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x106b50 0xc0 0xa (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x106b54 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x106b54) (andEaxImm32Effect 0x106b54 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106b54 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x106b54 0x3333) pre_rip
  have f39 : InstrSpec 0x106b59 [0x66, 0x41, 0xC1, 0xC5, 0x0E] (fun s => s.RIP = 0x106b59) (rolR16Effect 0x106b59 5 13 14)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b59 5 13 14).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106b59 0x41 0xc5 0xe (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (6, 93), (7, 55), (8, 91), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b12) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (6, 95), (7, 55), (8, 91), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b16) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (6, 95), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b19) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 85), (1, 99), (2, 57), (3, 65), (4, 4), (5, 79), (6, 95), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b1b) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 85), (1, 101), (2, 57), (3, 65), (4, 4), (5, 79), (6, 95), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b1f) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 85), (1, 101), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b25) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 85), (1, 105), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b2b) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 85), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b2d) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 109), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b30) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 111), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b34) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b39) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 115), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b3c) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 117), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b40) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 119), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b46) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b48) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.exec (n := 123) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b4d) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 124), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b50) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 126), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b54) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b59) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f39 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 130), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b5e) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106ab8_2 code

theorem rest_l106ab8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106ab8 bytes_l106ab8) (entryMap (live .l106ab8))
      138 0x106ab8 bytes_l106ab8 b_l106ab8 := by
  have f0 : InstrSpec 0x106ab8 [0x44, 0x8B, 0x4C, 0x24, 0x08] (LoadPre 0x106ab8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106ab8 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x106ab8 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x106ab8 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x106ab8 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106abd [0x8B, 0x7C, 0x24, 0x0C] (LoadPre 0x106abd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106abd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106abd 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x106abd 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x106abd 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106ac1 [0x0F, 0xB7, 0x54, 0x24, 0x0A] (LoadPre 0x106ac1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106ac1 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106ac1 5 2 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x106ac1 5 2 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m16_effect_step 0x106ac1 2 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106ac6 [0x44, 0x0F, 0xB7, 0x7C, 0x24, 0x0E] (LoadPre 0x106ac6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106ac6 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106ac6 6 15 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M16Effect_footprint 0x106ac6 6 15 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106ac6 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x106acc [0x44, 0x8B, 0x6C, 0x24, 0x10] (LoadPre 0x106acc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106acc + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x106acc 13 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x106acc 13 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x106acc 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x106ad1 [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x12] (LoadPre 0x106ad1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106ad1 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106ad1 6 10 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x106ad1 6 10 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106ad1 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x106ad7 [0x8B, 0x5C, 0x24, 0x14] (LoadPre 0x106ad7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106ad7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106ad7 3 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x106ad7 3 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x106ad7 3 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x106adb [0x44, 0x89, 0xC8] (fun s => s.RIP = 0x106adb) (movR32R32Effect 0x106adb 3 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106adb 3 0 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x106adb 0x44 0xc8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x106ade [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x106ade) (rolR16Effect 0x106ade 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x106ade 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x106ade 0xc0 0xa (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x106ae2 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x106ae2) (andEaxImm32Effect 0x106ae2 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106ae2 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x106ae2 0x3333) pre_rip
  have f10 : InstrSpec 0x106ae7 [0x44, 0x89, 0xCD] (fun s => s.RIP = 0x106ae7) (movR32R32Effect 0x106ae7 3 5 9)
      [.gpr 9] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x106ae7 3 5 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x106ae7 0x44 0xcd (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x106aea [0x66, 0xC1, 0xC5, 0x0E] (fun s => s.RIP = 0x106aea) (rolR16Effect 0x106aea 4 5 14)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR16Effect_footprint 0x106aea 4 5 14).toInstrSpec (rol_r16_imm8_effect_step 0x106aea 0xc5 0xe (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x106aee [0x81, 0xE5, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x106aee) (andR32Imm32Effect 0x106aee 6 5 0xffffcccc)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106aee 6 5 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x106aee 0xe5 0xffffcccc (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x106af4 [0x09, 0xC5] (fun s => s.RIP = 0x106af4) (orR32R32Effect 0x106af4 2 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (orR32R32Effect_footprint 0x106af4 2 5 0).toInstrSpec (or_r32_r32_effect_step 0x106af4 0xc5 (by decide)) pre_rip
  have f14 : InstrSpec 0x106af6 [0x89, 0xD0] (fun s => s.RIP = 0x106af6) (movR32R32Effect 0x106af6 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x106af6 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x106af6 0xd0 (by decide)) pre_rip
  have f15 : InstrSpec 0x106af8 [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x106af8) (rolR16Effect 0x106af8 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x106af8 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x106af8 0xc0 0xa (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x106afc [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x106afc) (andEaxImm32Effect 0x106afc 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x106afc 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x106afc 0x3333) pre_rip
  have f17 : InstrSpec 0x106b01 [0x41, 0x89, 0xD0] (fun s => s.RIP = 0x106b01) (movR32R32Effect 0x106b01 3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x106b01 3 8 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x106b01 0x41 0xd0 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x106b04 [0x66, 0x41, 0xC1, 0xC0, 0x0E] (fun s => s.RIP = 0x106b04) (rolR16Effect 0x106b04 5 8 14)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR16Effect_footprint 0x106b04 5 8 14).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106b04 0x41 0xc0 0xe (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x106b09 [0x41, 0x81, 0xE0, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x106b09) (andR32Imm32Effect 0x106b09 7 8 0xffffcccc)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106b09 7 8 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x106b09 0x41 0xe0 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (9, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106abd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (7, 55), (9, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ac1) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (7, 55), (9, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ac6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 4), (7, 55), (9, 53), (12, 12), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106acc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (4, 4), (7, 55), (9, 53), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ad1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 57), (4, 4), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ad7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 57), (3, 65), (4, 4), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106adb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (2, 57), (3, 65), (4, 4), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ade) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (2, 57), (3, 65), (4, 4), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ae2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (2, 57), (3, 65), (4, 4), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ae7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (2, 57), (3, 65), (4, 4), (5, 73), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106aea) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 71), (2, 57), (3, 65), (4, 4), (5, 75), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106aee) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (2, 57), (3, 65), (4, 4), (5, 77), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106af4) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106af6) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106af8) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106afc) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b01) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (8, 87), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b04) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (8, 89), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b09) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (8, 91), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106b10) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106ab8_1 code

theorem block_l106ab8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106ab8 :=
  Rest.liftedBlock (rest_l106ab8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106ab8 x hx)

theorem rest_l106ce3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106ce3 bytes_l106ce3) (entryMap (live .l106ce3))
      2 0x106ce3 bytes_l106ce3 b_l106ce3 := by
  have f0 : InstrSpec 0x106ce3 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x106ce3) (movR64R64Effect 0x106ce3 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106ce3 7 14).toInstrSpec (mov_r64_r64_effect_step 0x106ce3 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x106ce6 [0xE8, 0x95, 0x98, 0xFF, 0xFF] (PushPre 0x106ce6 5) (callEffect (fun _ => 0x100580) 0x106ceb)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106ce6 0x100580 0x106ceb).toInstrSpec (call_rel32_effect_step 0x106ce6 0xffff9895 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ce6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100580) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l106ce3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106ce3 :=
  Rest.liftedBlock (rest_l106ce3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106ce3 x hx)

theorem rest_l106ceb [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106ceb bytes_l106ceb) (entryMap (live .l106ceb))
      19 0x106ceb bytes_l106ceb b_l106ceb := by
  have f0 : InstrSpec 0x106ceb [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x22] (LoadPre 0x106ceb (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x22)) s (0x106ceb + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106ceb 6 0 (.sib 3 (some 12) 1 (.d8 0x22)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106ceb 6 0 (.sib 3 (some 12) 1 (.d8 0x22))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106ceb 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106cf1 [0x66, 0x31, 0x44, 0x24, 0x08] (StorePre 0x106cf1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106cf1 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106cf1 5 16 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106cf1 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m16_r16_effect_step 0x106cf1 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x106cf6 [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x24] (LoadPre 0x106cf6 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x24)) s (0x106cf6 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106cf6 6 0 (.sib 3 (some 12) 1 (.d8 0x24)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106cf6 6 0 (.sib 3 (some 12) 1 (.d8 0x24))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106cf6 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106cfc [0x66, 0x31, 0x44, 0x24, 0x0A] (StorePre 0x106cfc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106cfc + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106cfc 5 16 0 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106cfc 5 0 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (xor_m16_r16_effect_step 0x106cfc 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x106d01 [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x26] (LoadPre 0x106d01 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x26)) s (0x106d01 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d01 6 0 (.sib 3 (some 12) 1 (.d8 0x26)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106d01 6 0 (.sib 3 (some 12) 1 (.d8 0x26))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106d01 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x106d07 [0x66, 0x31, 0x44, 0x24, 0x0C] (StorePre 0x106d07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106d07 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d07 5 16 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106d07 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (xor_m16_r16_effect_step 0x106d07 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x106d0c [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x28] (LoadPre 0x106d0c (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x28)) s (0x106d0c + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d0c 6 0 (.sib 3 (some 12) 1 (.d8 0x28)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106d0c 6 0 (.sib 3 (some 12) 1 (.d8 0x28))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106d0c 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x106d12 [0x66, 0x31, 0x44, 0x24, 0x0E] (StorePre 0x106d12 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106d12 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d12 5 16 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106d12 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (xor_m16_r16_effect_step 0x106d12 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x106d17 [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x2A] (LoadPre 0x106d17 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2a)) s (0x106d17 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d17 6 0 (.sib 3 (some 12) 1 (.d8 0x2a)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106d17 6 0 (.sib 3 (some 12) 1 (.d8 0x2a))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106d17 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x106d1d [0x66, 0x31, 0x44, 0x24, 0x10] (StorePre 0x106d1d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106d1d + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d1d 5 16 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106d1d 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (xor_m16_r16_effect_step 0x106d1d 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x106d22 [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x2C] (LoadPre 0x106d22 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2c)) s (0x106d22 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d22 6 0 (.sib 3 (some 12) 1 (.d8 0x2c)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106d22 6 0 (.sib 3 (some 12) 1 (.d8 0x2c))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106d22 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x106d28 [0x66, 0x31, 0x44, 0x24, 0x12] (StorePre 0x106d28 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106d28 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d28 5 16 0 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106d28 5 0 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (xor_m16_r16_effect_step 0x106d28 0 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x106d2d [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x2E] (LoadPre 0x106d2d (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2e)) s (0x106d2d + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d2d 6 0 (.sib 3 (some 12) 1 (.d8 0x2e)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106d2d 6 0 (.sib 3 (some 12) 1 (.d8 0x2e))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106d2d 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x106d33 [0x66, 0x31, 0x44, 0x24, 0x14] (StorePre 0x106d33 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106d33 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d33 5 16 0 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106d33 5 0 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (xor_m16_r16_effect_step 0x106d33 0 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x106d38 [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x30] (LoadPre 0x106d38 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x30)) s (0x106d38 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d38 6 0 (.sib 3 (some 12) 1 (.d8 0x30)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106d38 6 0 (.sib 3 (some 12) 1 (.d8 0x30))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106d38 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x106d3e [0x66, 0x31, 0x44, 0x24, 0x16] (StorePre 0x106d3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106d3e + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d3e 5 16 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106d3e 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (xor_m16_r16_effect_step 0x106d3e 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x106d43 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106d43) (movR32Imm32Effect 0x106d43 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x106d43 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x106d43 0xbe (by decide) 0x8) pre_rip
  have f17 : InstrSpec 0x106d48 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x106d48) (movR64R64Effect 0x106d48 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106d48 7 14).toInstrSpec (mov_r64_r64_effect_step 0x106d48 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x106d4b [0xE8, 0xC0, 0x9D, 0xFF, 0xFF] (PushPre 0x106d4b 5) (callEffect (fun _ => 0x100b10) 0x106d50)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106d4b 0x100b10 0x106d50).toInstrSpec (call_rel32_effect_step 0x106d4b 0xffff9dc0 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cf1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cf6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106cfc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d01) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d07) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d0c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d12) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d17) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d1d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d22) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d28) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d2d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d33) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d38) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d3e) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d43) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (6, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d48) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d4b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 74), (3, 3), (4, 81), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f18 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 83) (by decide) (by decide) rfl rfl

theorem block_l106ceb [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106ceb :=
  Rest.liftedBlock (rest_l106ceb code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106ceb x hx)

theorem rest_l106d50_4 [Bindings] (code : CodeMap) :
    Rest (n := 202) code lifted (codeRange 0x106d50 bytes_l106d50) [(0, 152), (1, 200), (2, 187), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]
      14 0x106e85 bytes_l106d50_4 b_l106d50_4 := by
  have f80 : InstrSpec 0x106e85 [0x31, 0xCF] (fun s => s.RIP = 0x106e85) (xorR32R32Effect 0x106e85 2 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e85 2 7 1).toInstrSpec (xor_r32_r32_effect_step 0x106e85 0xcf (by decide)) pre_rip
  have f81 : InstrSpec 0x106e87 [0x31, 0xCA] (fun s => s.RIP = 0x106e87) (xorR32R32Effect 0x106e87 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e87 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x106e87 0xca (by decide)) pre_rip
  have f82 : InstrSpec 0x106e89 [0x89, 0xF9] (fun s => s.RIP = 0x106e89) (movR32R32Effect 0x106e89 2 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106e89 2 1 7).toInstrSpec (mov_r32_r32_effect_step 0x106e89 0xf9 (by decide)) pre_rip
  have f83 : InstrSpec 0x106e8b [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x106e8b) (rolR16Effect 0x106e8b 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x106e8b 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x106e8b 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x106e8f [0x66, 0x42, 0x33, 0x4C, 0x63, 0x3C] (LoadPre 0x106e8f (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3c)) s (0x106e8f + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e8f 6 1 (.sib 3 (some 12) 1 (.d8 0x3c)))
      [.gpr 1, .gpr 3, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106e8f 6 1 (.sib 3 (some 12) 1 (.d8 0x3c))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106e8f 0x42 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f85 : InstrSpec 0x106e95 [0x31, 0xCA] (fun s => s.RIP = 0x106e95) (xorR32R32Effect 0x106e95 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e95 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x106e95 0xca (by decide)) pre_rip
  have f86 : InstrSpec 0x106e97 [0x66, 0x89, 0x54, 0x24, 0x12] (StorePre 0x106e97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106e97 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106e97 5 2 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106e97 5 2 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (mov_m16_r16_effect_step 0x106e97 2 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f87 : InstrSpec 0x106e9c [0x66, 0x41, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x106e9c) (rolR16Effect 0x106e9c 5 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR16Effect_footprint 0x106e9c 5 8 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106e9c 0x41 0xc0 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x106ea1 [0x66, 0x46, 0x33, 0x44, 0x63, 0x3E] (LoadPre 0x106ea1 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3e)) s (0x106ea1 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106ea1 6 8 (.sib 3 (some 12) 1 (.d8 0x3e)))
      [.gpr 8, .gpr 3, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106ea1 6 8 (.sib 3 (some 12) 1 (.d8 0x3e))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106ea1 0x46 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f89 : InstrSpec 0x106ea7 [0x33, 0x7C, 0x24, 0x24] (LoadPre 0x106ea7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106ea7 + BitVec.ofNat 64 4)) 4) (xorR32M32LowEffect 0x106ea7 7 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 7, .gpr 4] [] [.reg 7, .flags, .rip] :=
    (xorR32M32LowEffect_footprint 0x106ea7 7 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (xor_r32_m32_low_effect_step 0x106ea7 7 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f90 : InstrSpec 0x106eab [0x44, 0x31, 0xC7] (fun s => s.RIP = 0x106eab) (xorR32R32Effect 0x106eab 3 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106eab 3 7 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x106eab 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x106eae [0x66, 0x89, 0x7C, 0x24, 0x14] (StorePre 0x106eae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106eae + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106eae 5 7 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106eae 5 7 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m16_r16_effect_step 0x106eae 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f92 : InstrSpec 0x106eb3 [0x49, 0x83, 0xC4, 0x20] (fun s => s.RIP = 0x106eb3) (addR64Imm8Effect 0x106eb3 12 0x20)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x106eb3 12 0x20).toInstrSpec (add_r64_imm8_effect_step 0x106eb3 0x49 0xc4 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f80 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 152), (1, 200), (2, 187), (3, 3), (4, 4), (5, 148), (6, 177), (7, 202), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e87) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f81 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 152), (1, 200), (2, 204), (3, 3), (4, 4), (5, 148), (6, 177), (7, 202), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e89) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f82 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 152), (1, 206), (2, 204), (3, 3), (4, 4), (5, 148), (6, 177), (7, 202), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e8b) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f83 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 152), (1, 208), (2, 204), (3, 3), (4, 4), (5, 148), (6, 177), (7, 202), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e8f) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f84 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 152), (1, 210), (2, 204), (3, 3), (4, 4), (5, 148), (6, 177), (7, 202), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e95) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f85 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 152), (1, 210), (2, 212), (3, 3), (4, 4), (5, 148), (6, 177), (7, 202), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e97) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.exec (n := 214) (ρ' := [(0, 152), (1, 210), (2, 212), (3, 3), (4, 4), (5, 148), (6, 177), (7, 202), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e9c) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f87 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 152), (1, 210), (2, 212), (3, 3), (4, 4), (5, 148), (6, 177), (7, 202), (8, 215), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ea1) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f88 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 152), (1, 210), (2, 212), (3, 3), (4, 4), (5, 148), (6, 177), (7, 202), (8, 217), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ea7) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f89 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 152), (1, 210), (2, 212), (3, 3), (4, 4), (5, 148), (6, 177), (7, 219), (8, 217), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106eab) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f90 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 152), (1, 210), (2, 212), (3, 3), (4, 4), (5, 148), (6, 177), (7, 221), (8, 217), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106eae) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.exec (n := 223) (ρ' := [(0, 152), (1, 210), (2, 212), (3, 3), (4, 4), (5, 148), (6, 177), (7, 221), (8, 217), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106eb3) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f92 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 152), (1, 210), (2, 212), (3, 3), (4, 4), (5, 148), (6, 177), (7, 221), (8, 217), (9, 195), (10, 111), (11, 168), (12, 224), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106eb7) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 226) (jmp_rel32_effect_step 0x106eb7 0xfffffb34 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l106d50_3 [Bindings] (code : CodeMap) :
    Rest (n := 166) code lifted (codeRange 0x106d50 bytes_l106d50) [(0, 152), (1, 164), (2, 144), (3, 3), (4, 4), (5, 148), (6, 160), (7, 156), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]
      34 0x106e2d bytes_l106d50_3 b_l106d50_3 := by
  have f60 : InstrSpec 0x106e2d [0x66, 0x42, 0x33, 0x4C, 0x63, 0x34] (LoadPre 0x106e2d (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x34)) s (0x106e2d + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e2d 6 1 (.sib 3 (some 12) 1 (.d8 0x34)))
      [.gpr 1, .gpr 3, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106e2d 6 1 (.sib 3 (some 12) 1 (.d8 0x34))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106e2d 0x42 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f61 : InstrSpec 0x106e33 [0x41, 0x31, 0xCB] (fun s => s.RIP = 0x106e33) (xorR32R32Effect 0x106e33 3 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e33 3 11 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x106e33 0x41 0xcb (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x106e36 [0x66, 0x44, 0x89, 0x5C, 0x24, 0x0A] (StorePre 0x106e36 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106e36 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106e36 6 11 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106e36 6 11 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106e36 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f63 : InstrSpec 0x106e3c [0x66, 0x41, 0xC1, 0xC5, 0x08] (fun s => s.RIP = 0x106e3c) (rolR16Effect 0x106e3c 5 13 8)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR16Effect_footprint 0x106e3c 5 13 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106e3c 0x41 0xc5 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x106e41 [0x66, 0x46, 0x33, 0x6C, 0x63, 0x36] (LoadPre 0x106e41 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x36)) s (0x106e41 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e41 6 13 (.sib 3 (some 12) 1 (.d8 0x36)))
      [.gpr 13, .gpr 3, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106e41 6 13 (.sib 3 (some 12) 1 (.d8 0x36))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106e41 0x46 (by decide) 5 (.sib 3 (some 12) 1 (.d8 0x36)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f65 : InstrSpec 0x106e47 [0x33, 0x74, 0x24, 0x20] (LoadPre 0x106e47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106e47 + BitVec.ofNat 64 4)) 4) (xorR32M32LowEffect 0x106e47 6 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (xorR32M32LowEffect_footprint 0x106e47 6 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (xor_r32_m32_low_effect_step 0x106e47 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f66 : InstrSpec 0x106e4b [0x44, 0x31, 0xEE] (fun s => s.RIP = 0x106e4b) (xorR32R32Effect 0x106e4b 3 6 13)
      [.gpr 6, .gpr 13] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e4b 3 6 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x106e4b 0x44 0xee (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x106e4e [0x66, 0x41, 0xC1, 0xC7, 0x08] (fun s => s.RIP = 0x106e4e) (rolR16Effect 0x106e4e 5 15 8)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR16Effect_footprint 0x106e4e 5 15 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106e4e 0x41 0xc7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x106e53 [0x66, 0x89, 0x74, 0x24, 0x0C] (StorePre 0x106e53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106e53 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106e53 5 6 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106e53 5 6 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x106e53 6 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f69 : InstrSpec 0x106e58 [0x66, 0x46, 0x33, 0x7C, 0x63, 0x38] (LoadPre 0x106e58 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x38)) s (0x106e58 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e58 6 15 (.sib 3 (some 12) 1 (.d8 0x38)))
      [.gpr 15, .gpr 3, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106e58 6 15 (.sib 3 (some 12) 1 (.d8 0x38))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106e58 0x46 (by decide) 7 (.sib 3 (some 12) 1 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f70 : InstrSpec 0x106e5e [0x44, 0x31, 0xFA] (fun s => s.RIP = 0x106e5e) (xorR32R32Effect 0x106e5e 3 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e5e 3 2 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x106e5e 0x44 0xfa (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x106e61 [0x66, 0x89, 0x54, 0x24, 0x0E] (StorePre 0x106e61 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106e61 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106e61 5 2 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106e61 5 2 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x106e61 2 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f72 : InstrSpec 0x106e66 [0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x106e66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x106e66 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106e66 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x106e66 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x106e66 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f73 : InstrSpec 0x106e6a [0x89, 0xD1] (fun s => s.RIP = 0x106e6a) (movR32R32Effect 0x106e6a 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106e6a 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x106e6a 0xd1 (by decide)) pre_rip
  have f74 : InstrSpec 0x106e6c [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x106e6c) (rolR16Effect 0x106e6c 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x106e6c 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x106e6c 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x106e70 [0x66, 0x42, 0x33, 0x4C, 0x63, 0x3A] (LoadPre 0x106e70 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3a)) s (0x106e70 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e70 6 1 (.sib 3 (some 12) 1 (.d8 0x3a)))
      [.gpr 1, .gpr 3, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106e70 6 1 (.sib 3 (some 12) 1 (.d8 0x3a))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106e70 0x42 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x3a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x106e76 [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x106e76) (xorR32R32Effect 0x106e76 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e76 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x106e76 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x106e79 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x106e79 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106e79 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106e79 6 9 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106e79 6 9 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106e79 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x106e7f [0x89, 0xF9] (fun s => s.RIP = 0x106e7f) (movR32R32Effect 0x106e7f 2 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106e7f 2 1 7).toInstrSpec (mov_r32_r32_effect_step 0x106e7f 0xf9 (by decide)) pre_rip
  have f79 : InstrSpec 0x106e81 [0x66, 0xC1, 0xC1, 0x0C] (fun s => s.RIP = 0x106e81) (rolR16Effect 0x106e81 4 1 12)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x106e81 4 1 12).toInstrSpec (rol_r16_imm8_effect_step 0x106e81 0xc1 0xc (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f60 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 152), (1, 166), (2, 144), (3, 3), (4, 4), (5, 148), (6, 160), (7, 156), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e33) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f61 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 152), (1, 166), (2, 144), (3, 3), (4, 4), (5, 148), (6, 160), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e36) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.exec (n := 170) (ρ' := [(0, 152), (1, 166), (2, 144), (3, 3), (4, 4), (5, 148), (6, 160), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e3c) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f63 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 152), (1, 166), (2, 144), (3, 3), (4, 4), (5, 148), (6, 160), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 171), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e41) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f64 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 152), (1, 166), (2, 144), (3, 3), (4, 4), (5, 148), (6, 160), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e47) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f65 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 152), (1, 166), (2, 144), (3, 3), (4, 4), (5, 148), (6, 175), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e4b) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f66 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 152), (1, 166), (2, 144), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e4e) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f67 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 152), (1, 166), (2, 144), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e53) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.exec (n := 181) (ρ' := [(0, 152), (1, 166), (2, 144), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e58) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f69 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 152), (1, 166), (2, 144), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e5e) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f70 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 152), (1, 166), (2, 184), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e61) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(0, 152), (1, 166), (2, 184), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e66) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f72 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 152), (1, 166), (2, 187), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e6a) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f73 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 152), (1, 189), (2, 187), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e6c) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f74 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 152), (1, 191), (2, 187), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e70) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f75 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 152), (1, 193), (2, 187), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 146), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e76) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f76 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 152), (1, 193), (2, 187), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e79) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.exec (n := 197) (ρ' := [(0, 152), (1, 193), (2, 187), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e7f) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f78 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 152), (1, 198), (2, 187), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e81) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f79 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 152), (1, 200), (2, 187), (3, 3), (4, 4), (5, 148), (6, 177), (7, 156), (8, 122), (9, 195), (10, 111), (11, 168), (12, 105), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e85) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106d50_4 code

theorem rest_l106d50_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x106d50 bytes_l106d50) [(0, 124), (1, 93), (2, 107), (3, 3), (4, 4), (5, 120), (6, 113), (7, 126), (8, 122), (9, 109), (10, 111), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]
      54 0x106de6 bytes_l106d50_2 b_l106d50_2 := by
  have f40 : InstrSpec 0x106de6 [0x45, 0x31, 0xEB] (fun s => s.RIP = 0x106de6) (xorR32R32Effect 0x106de6 3 11 13)
      [.gpr 11, .gpr 13] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106de6 3 11 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x106de6 0x45 0xeb (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x106de9 [0x41, 0x89, 0xD5] (fun s => s.RIP = 0x106de9) (movR32R32Effect 0x106de9 3 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x106de9 3 13 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x106de9 0x41 0xd5 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x106dec [0x44, 0x31, 0xD2] (fun s => s.RIP = 0x106dec) (xorR32R32Effect 0x106dec 3 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106dec 3 2 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x106dec 0x44 0xd2 (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x106def [0x45, 0x89, 0xCF] (fun s => s.RIP = 0x106def) (movR32R32Effect 0x106def 3 15 9)
      [.gpr 9] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x106def 3 15 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x106def 0x45 0xcf (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x106df2 [0x41, 0x31, 0xF1] (fun s => s.RIP = 0x106df2) (xorR32R32Effect 0x106df2 3 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106df2 3 9 6).toInstrSpec (xor_r32_r32_rex_effect_step 0x106df2 0x41 0xf1 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x106df5 [0x66, 0xC1, 0xC7, 0x08] (fun s => s.RIP = 0x106df5) (rolR16Effect 0x106df5 4 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR16Effect_footprint 0x106df5 4 7 8).toInstrSpec (rol_r16_imm8_effect_step 0x106df5 0xc7 0x8 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x106df9 [0x41, 0x31, 0xEE] (fun s => s.RIP = 0x106df9) (xorR32R32Effect 0x106df9 3 14 5)
      [.gpr 14, .gpr 5] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106df9 3 14 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x106df9 0x41 0xee (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x106dfc [0x41, 0x31, 0xEB] (fun s => s.RIP = 0x106dfc) (xorR32R32Effect 0x106dfc 3 11 5)
      [.gpr 11, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106dfc 3 11 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x106dfc 0x41 0xeb (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x106dff [0x31, 0xEA] (fun s => s.RIP = 0x106dff) (xorR32R32Effect 0x106dff 2 2 5)
      [.gpr 2, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106dff 2 2 5).toInstrSpec (xor_r32_r32_effect_step 0x106dff 0xea (by decide)) pre_rip
  have f49 : InstrSpec 0x106e01 [0x41, 0x31, 0xE9] (fun s => s.RIP = 0x106e01) (xorR32R32Effect 0x106e01 3 9 5)
      [.gpr 9, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e01 3 9 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x106e01 0x41 0xe9 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x106e04 [0x66, 0xC1, 0xC5, 0x08] (fun s => s.RIP = 0x106e04) (rolR16Effect 0x106e04 4 5 8)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR16Effect_footprint 0x106e04 4 5 8).toInstrSpec (rol_r16_imm8_effect_step 0x106e04 0xc5 0x8 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x106e08 [0x66, 0x42, 0x33, 0x7C, 0x63, 0x32] (LoadPre 0x106e08 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x32)) s (0x106e08 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e08 6 7 (.sib 3 (some 12) 1 (.d8 0x32)))
      [.gpr 7, .gpr 3, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x106e08 6 7 (.sib 3 (some 12) 1 (.d8 0x32))).toInstrSpec (xor_r16_m16_rex_effect_step 0x106e08 0x42 (by decide) 7 (.sib 3 (some 12) 1 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f52 : InstrSpec 0x106e0e [0x31, 0xE8] (fun s => s.RIP = 0x106e0e) (xorR32R32Effect 0x106e0e 2 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e0e 2 0 5).toInstrSpec (xor_r32_r32_effect_step 0x106e0e 0xe8 (by decide)) pre_rip
  have f53 : InstrSpec 0x106e10 [0x41, 0x31, 0xFE] (fun s => s.RIP = 0x106e10) (xorR32R32Effect 0x106e10 3 14 7)
      [.gpr 14, .gpr 7] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106e10 3 14 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x106e10 0x41 0xfe (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x106e13 [0x0F, 0xB7, 0x7C, 0x24, 0x12] (LoadPre 0x106e13 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106e13 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106e13 5 7 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x106e13 5 7 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (movzx_r32_m16_effect_step 0x106e13 7 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x106e18 [0x66, 0x89, 0x44, 0x24, 0x16] (StorePre 0x106e18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106e18 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106e18 5 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106e18 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m16_r16_effect_step 0x106e18 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x106e1d [0x66, 0x44, 0x89, 0x74, 0x24, 0x08] (StorePre 0x106e1d 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106e1d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106e1d 6 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106e1d 6 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106e1d 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x106e23 [0x8B, 0x74, 0x24, 0x3C] (LoadPre 0x106e23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x106e23 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106e23 6 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x106e23 6 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_r32_m32_low_effect_step 0x106e23 6 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f58 : InstrSpec 0x106e27 [0x89, 0xF1] (fun s => s.RIP = 0x106e27) (movR32R32Effect 0x106e27 2 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106e27 2 1 6).toInstrSpec (mov_r32_r32_effect_step 0x106e27 0xf1 (by decide)) pre_rip
  have f59 : InstrSpec 0x106e29 [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x106e29) (rolR16Effect 0x106e29 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x106e29 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x106e29 0xc1 0x8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 124), (1, 93), (2, 107), (3, 3), (4, 4), (5, 120), (6, 113), (7, 126), (8, 122), (9, 109), (10, 111), (11, 128), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106de9) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f41 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 124), (1, 93), (2, 107), (3, 3), (4, 4), (5, 120), (6, 113), (7, 126), (8, 122), (9, 109), (10, 111), (11, 128), (12, 105), (13, 130), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dec) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 124), (1, 93), (2, 132), (3, 3), (4, 4), (5, 120), (6, 113), (7, 126), (8, 122), (9, 109), (10, 111), (11, 128), (12, 105), (13, 130), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106def) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 124), (1, 93), (2, 132), (3, 3), (4, 4), (5, 120), (6, 113), (7, 126), (8, 122), (9, 109), (10, 111), (11, 128), (12, 105), (13, 130), (14, 61), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106df2) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f44 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 124), (1, 93), (2, 132), (3, 3), (4, 4), (5, 120), (6, 113), (7, 126), (8, 122), (9, 136), (10, 111), (11, 128), (12, 105), (13, 130), (14, 61), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106df5) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 124), (1, 93), (2, 132), (3, 3), (4, 4), (5, 120), (6, 113), (7, 138), (8, 122), (9, 136), (10, 111), (11, 128), (12, 105), (13, 130), (14, 61), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106df9) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f46 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 124), (1, 93), (2, 132), (3, 3), (4, 4), (5, 120), (6, 113), (7, 138), (8, 122), (9, 136), (10, 111), (11, 128), (12, 105), (13, 130), (14, 140), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dfc) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f47 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 124), (1, 93), (2, 132), (3, 3), (4, 4), (5, 120), (6, 113), (7, 138), (8, 122), (9, 136), (10, 111), (11, 142), (12, 105), (13, 130), (14, 140), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dff) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 124), (1, 93), (2, 144), (3, 3), (4, 4), (5, 120), (6, 113), (7, 138), (8, 122), (9, 136), (10, 111), (11, 142), (12, 105), (13, 130), (14, 140), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e01) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f49 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 124), (1, 93), (2, 144), (3, 3), (4, 4), (5, 120), (6, 113), (7, 138), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 140), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e04) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f50 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 124), (1, 93), (2, 144), (3, 3), (4, 4), (5, 148), (6, 113), (7, 138), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 140), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e08) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f51 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 124), (1, 93), (2, 144), (3, 3), (4, 4), (5, 148), (6, 113), (7, 150), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 140), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e0e) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f52 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 152), (1, 93), (2, 144), (3, 3), (4, 4), (5, 148), (6, 113), (7, 150), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 140), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e10) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f53 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 152), (1, 93), (2, 144), (3, 3), (4, 4), (5, 148), (6, 113), (7, 150), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e13) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.out (n := 156) f54 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 157) (ρ' := [(0, 152), (1, 93), (2, 144), (3, 3), (4, 4), (5, 148), (6, 113), (7, 156), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e18) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 158) (RestInside.exec (n := 158) (ρ' := [(0, 152), (1, 93), (2, 144), (3, 3), (4, 4), (5, 148), (6, 113), (7, 156), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e1d) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 159) (RestInside.exec (n := 159) (ρ' := [(0, 152), (1, 93), (2, 144), (3, 3), (4, 4), (5, 148), (6, 113), (7, 156), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e23) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f57 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 152), (1, 93), (2, 144), (3, 3), (4, 4), (5, 148), (6, 160), (7, 156), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e27) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 152), (1, 162), (2, 144), (3, 3), (4, 4), (5, 148), (6, 160), (7, 156), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e29) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 152), (1, 164), (2, 144), (3, 3), (4, 4), (5, 148), (6, 160), (7, 156), (8, 122), (9, 146), (10, 111), (11, 142), (12, 105), (13, 130), (14, 154), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106e2d) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106d50_3 code

theorem rest_l106d50_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x106d50 bytes_l106d50) [(0, 79), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]
      74 0x106da6 bytes_l106d50_1 b_l106d50_1 := by
  have f20 : InstrSpec 0x106da6 [0x89, 0xC1] (fun s => s.RIP = 0x106da6) (movR32R32Effect 0x106da6 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x106da6 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x106da6 0xc1 (by decide)) pre_rip
  have f21 : InstrSpec 0x106da8 [0x66, 0xC1, 0xC1, 0x0C] (fun s => s.RIP = 0x106da8) (rolR16Effect 0x106da8 4 1 12)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x106da8 4 1 12).toInstrSpec (rol_r16_imm8_effect_step 0x106da8 0xc1 0xc (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x106dac [0x89, 0x4C, 0x24, 0x24] (StorePre 0x106dac 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106dac + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x106dac 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x106dac 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_m32_r32_low_effect_step 0x106dac 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x106db0 [0x89, 0xEF] (fun s => s.RIP = 0x106db0) (movR32R32Effect 0x106db0 2 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x106db0 2 7 5).toInstrSpec (mov_r32_r32_effect_step 0x106db0 0xef (by decide)) pre_rip
  have f24 : InstrSpec 0x106db2 [0x66, 0xC1, 0xC7, 0x0C] (fun s => s.RIP = 0x106db2) (rolR16Effect 0x106db2 4 7 12)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR16Effect_footprint 0x106db2 4 7 12).toInstrSpec (rol_r16_imm8_effect_step 0x106db2 0xc7 0xc (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x106db6 [0x45, 0x31, 0xF3] (fun s => s.RIP = 0x106db6) (xorR32R32Effect 0x106db6 3 11 14)
      [.gpr 11, .gpr 14] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106db6 3 11 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x106db6 0x45 0xf3 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x106db9 [0x45, 0x31, 0xEC] (fun s => s.RIP = 0x106db9) (xorR32R32Effect 0x106db9 3 12 13)
      [.gpr 12, .gpr 13] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106db9 3 12 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x106db9 0x45 0xec (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x106dbc [0x44, 0x89, 0x64, 0x24, 0x3C] (StorePre 0x106dbc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x106dbc + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106dbc 12 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x106dbc 12 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m32_r32_effect_step 0x106dbc 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x106dc1 [0x4C, 0x8B, 0x64, 0x24, 0x28] (LoadPre 0x106dc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106dc1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106dc1 12 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x106dc1 12 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x106dc1 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x106dc6 [0x44, 0x31, 0xD2] (fun s => s.RIP = 0x106dc6) (xorR32R32Effect 0x106dc6 3 2 10)
      [.gpr 2, .gpr 10] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106dc6 3 2 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x106dc6 0x44 0xd2 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x106dc9 [0x41, 0x31, 0xF1] (fun s => s.RIP = 0x106dc9) (xorR32R32Effect 0x106dc9 3 9 6)
      [.gpr 9, .gpr 6] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106dc9 3 9 6).toInstrSpec (xor_r32_r32_rex_effect_step 0x106dc9 0x41 0xf1 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x106dcc [0x41, 0x89, 0xF2] (fun s => s.RIP = 0x106dcc) (movR32R32Effect 0x106dcc 3 10 6)
      [.gpr 6] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x106dcc 3 10 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x106dcc 0x41 0xf2 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x106dcf [0x44, 0x89, 0xFE] (fun s => s.RIP = 0x106dcf) (movR32R32Effect 0x106dcf 3 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x106dcf 3 6 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x106dcf 0x44 0xfe (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x106dd2 [0x45, 0x31, 0xF8] (fun s => s.RIP = 0x106dd2) (xorR32R32Effect 0x106dd2 3 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106dd2 3 8 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x106dd2 0x45 0xf8 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x106dd5 [0x44, 0x89, 0x44, 0x24, 0x1C] (StorePre 0x106dd5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x106dd5 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106dd5 8 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x106dd5 8 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m32_r32_effect_step 0x106dd5 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x106dda [0x31, 0xC8] (fun s => s.RIP = 0x106dda) (xorR32R32Effect 0x106dda 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106dda 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106dda 0xc8 (by decide)) pre_rip
  have f36 : InstrSpec 0x106ddc [0x31, 0xFD] (fun s => s.RIP = 0x106ddc) (xorR32R32Effect 0x106ddc 2 5 7)
      [.gpr 5, .gpr 7] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106ddc 2 5 7).toInstrSpec (xor_r32_r32_effect_step 0x106ddc 0xfd (by decide)) pre_rip
  have f37 : InstrSpec 0x106dde [0x41, 0x89, 0xC0] (fun s => s.RIP = 0x106dde) (movR32R32Effect 0x106dde 3 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x106dde 3 8 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x106dde 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x106de1 [0x31, 0xF8] (fun s => s.RIP = 0x106de1) (xorR32R32Effect 0x106de1 2 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106de1 2 0 7).toInstrSpec (xor_r32_r32_effect_step 0x106de1 0xf8 (by decide)) pre_rip
  have f39 : InstrSpec 0x106de3 [0x44, 0x89, 0xDF] (fun s => s.RIP = 0x106de3) (movR32R32Effect 0x106de3 3 7 11)
      [.gpr 11] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x106de3 3 7 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x106de3 0x44 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 79), (1, 91), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106da8) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 79), (1, 93), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dac) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 79), (1, 93), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106db0) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 79), (1, 93), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (7, 96), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106db2) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 79), (1, 93), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (7, 98), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106db6) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 79), (1, 93), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (7, 98), (8, 72), (9, 63), (10, 76), (11, 100), (12, 68), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106db9) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 79), (1, 93), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (7, 98), (8, 72), (9, 63), (10, 76), (11, 100), (12, 102), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dbc) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.exec (n := 104) (ρ' := [(0, 79), (1, 93), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (7, 98), (8, 72), (9, 63), (10, 76), (11, 100), (12, 102), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dc1) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f28 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 79), (1, 93), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (7, 98), (8, 72), (9, 63), (10, 76), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dc6) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f29 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 79), (1, 93), (2, 107), (3, 3), (4, 4), (5, 85), (6, 83), (7, 98), (8, 72), (9, 63), (10, 76), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dc9) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f30 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 79), (1, 93), (2, 107), (3, 3), (4, 4), (5, 85), (6, 83), (7, 98), (8, 72), (9, 109), (10, 76), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dcc) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f31 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 79), (1, 93), (2, 107), (3, 3), (4, 4), (5, 85), (6, 83), (7, 98), (8, 72), (9, 109), (10, 111), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dcf) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 79), (1, 93), (2, 107), (3, 3), (4, 4), (5, 85), (6, 113), (7, 98), (8, 72), (9, 109), (10, 111), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd2) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 79), (1, 93), (2, 107), (3, 3), (4, 4), (5, 85), (6, 113), (7, 98), (8, 115), (9, 109), (10, 111), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dd5) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.exec (n := 117) (ρ' := [(0, 79), (1, 93), (2, 107), (3, 3), (4, 4), (5, 85), (6, 113), (7, 98), (8, 115), (9, 109), (10, 111), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dda) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f35 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 118), (1, 93), (2, 107), (3, 3), (4, 4), (5, 85), (6, 113), (7, 98), (8, 115), (9, 109), (10, 111), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ddc) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.out (n := 120) f36 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 121) (ρ' := [(0, 118), (1, 93), (2, 107), (3, 3), (4, 4), (5, 120), (6, 113), (7, 98), (8, 115), (9, 109), (10, 111), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106dde) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 122) (RestInside.out (n := 122) f37 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 123) (ρ' := [(0, 118), (1, 93), (2, 107), (3, 3), (4, 4), (5, 120), (6, 113), (7, 98), (8, 122), (9, 109), (10, 111), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106de1) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 124), (1, 93), (2, 107), (3, 3), (4, 4), (5, 120), (6, 113), (7, 98), (8, 122), (9, 109), (10, 111), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106de3) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f39 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 124), (1, 93), (2, 107), (3, 3), (4, 4), (5, 120), (6, 113), (7, 126), (8, 122), (9, 109), (10, 111), (11, 100), (12, 105), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106de6) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106d50_2 code

theorem rest_l106d50 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106d50 bytes_l106d50) (entryMap (live .l106d50))
      94 0x106d50 bytes_l106d50 b_l106d50 := by
  have f0 : InstrSpec 0x106d50 [0x44, 0x8B, 0x5C, 0x24, 0x08] (LoadPre 0x106d50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106d50 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x106d50 11 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x106d50 11 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x106d50 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106d55 [0x8B, 0x54, 0x24, 0x0C] (LoadPre 0x106d55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106d55 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106d55 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x106d55 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x106d55 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106d59 [0x0F, 0xB7, 0x44, 0x24, 0x0A] (LoadPre 0x106d59 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106d59 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106d59 5 0 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106d59 5 0 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m16_effect_step 0x106d59 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x106d5e [0x45, 0x89, 0xDE] (fun s => s.RIP = 0x106d5e) (movR32R32Effect 0x106d5e 3 14 11)
      [.gpr 11] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x106d5e 3 14 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x106d5e 0x45 0xde (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x106d61 [0x66, 0x41, 0xC1, 0xC6, 0x0C] (fun s => s.RIP = 0x106d61) (rolR16Effect 0x106d61 5 14 12)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR16Effect_footprint 0x106d61 5 14 12).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106d61 0x41 0xc6 0xc (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x106d66 [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x0E] (LoadPre 0x106d66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106d66 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d66 6 9 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x106d66 6 9 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x106d66 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x106d6c [0x41, 0x89, 0xC5] (fun s => s.RIP = 0x106d6c) (movR32R32Effect 0x106d6c 3 13 0)
      [.gpr 0] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x106d6c 3 13 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x106d6c 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x106d6f [0x4C, 0x89, 0x64, 0x24, 0x28] (StorePre 0x106d6f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106d6f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106d6f 12 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x106d6f 12 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x106d6f 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x106d74 [0x41, 0x89, 0xC4] (fun s => s.RIP = 0x106d74) (movR32R32Effect 0x106d74 3 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x106d74 3 12 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x106d74 0x41 0xc4 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x106d77 [0x66, 0x41, 0xC1, 0xC5, 0x0C] (fun s => s.RIP = 0x106d77) (rolR16Effect 0x106d77 5 13 12)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR16Effect_footprint 0x106d77 5 13 12).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106d77 0x41 0xc5 0xc (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x106d7c [0x44, 0x8B, 0x44, 0x24, 0x10] (LoadPre 0x106d7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106d7c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x106d7c 8 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x106d7c 8 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x106d7c 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x106d81 [0x41, 0x89, 0xD2] (fun s => s.RIP = 0x106d81) (movR32R32Effect 0x106d81 3 10 2)
      [.gpr 2] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x106d81 3 10 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x106d81 0x41 0xd2 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x106d84 [0x66, 0x41, 0xC1, 0xC2, 0x0C] (fun s => s.RIP = 0x106d84) (rolR16Effect 0x106d84 5 10 12)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x106d84 5 10 12).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106d84 0x41 0xc2 0xc (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x106d89 [0x44, 0x89, 0x54, 0x24, 0x20] (StorePre 0x106d89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106d89 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106d89 10 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x106d89 10 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_effect_step 0x106d89 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x106d8e [0x8B, 0x44, 0x24, 0x14] (LoadPre 0x106d8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106d8e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106d8e 0 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x106d8e 0 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x106d8e 0 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x106d92 [0x44, 0x89, 0xCE] (fun s => s.RIP = 0x106d92) (movR32R32Effect 0x106d92 3 6 9)
      [.gpr 9] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x106d92 3 6 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x106d92 0x44 0xce (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x106d95 [0x66, 0xC1, 0xC6, 0x0C] (fun s => s.RIP = 0x106d95) (rolR16Effect 0x106d95 4 6 12)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR16Effect_footprint 0x106d95 4 6 12).toInstrSpec (rol_r16_imm8_effect_step 0x106d95 0xc6 0xc (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x106d99 [0x0F, 0xB7, 0x6C, 0x24, 0x16] (LoadPre 0x106d99 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106d99 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106d99 5 5 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M16Effect_footprint 0x106d99 5 5 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m16_effect_step 0x106d99 5 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x106d9e [0x45, 0x89, 0xC7] (fun s => s.RIP = 0x106d9e) (movR32R32Effect 0x106d9e 3 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x106d9e 3 15 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x106d9e 0x45 0xc7 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x106da1 [0x66, 0x41, 0xC1, 0xC7, 0x0C] (fun s => s.RIP = 0x106da1) (rolR16Effect 0x106da1 5 15 12)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR16Effect_footprint 0x106da1 5 15 12).toInstrSpec (rol_r16_imm8_rex_effect_step 0x106da1 0x41 0xc7 0xc (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (11, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d55) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (11, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d59) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (11, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d5e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (11, 53), (12, 12), (14, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d61) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (11, 53), (12, 12), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d66) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (9, 63), (11, 53), (12, 12), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d6c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (9, 63), (11, 53), (12, 12), (13, 65), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d6f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (9, 63), (11, 53), (12, 12), (13, 65), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d74) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (9, 63), (11, 53), (12, 68), (13, 65), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d77) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (9, 63), (11, 53), (12, 68), (13, 70), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d7c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (8, 72), (9, 63), (11, 53), (12, 68), (13, 70), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d81) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (8, 72), (9, 63), (10, 74), (11, 53), (12, 68), (13, 70), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d84) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d89) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 57), (2, 55), (3, 3), (4, 4), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d8e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (2, 55), (3, 3), (4, 4), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d92) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 79), (2, 55), (3, 3), (4, 4), (6, 81), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d95) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 79), (2, 55), (3, 3), (4, 4), (6, 83), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d99) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 79), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106d9e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 79), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106da1) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 79), (2, 55), (3, 3), (4, 4), (5, 85), (6, 83), (8, 72), (9, 63), (10, 76), (11, 53), (12, 68), (13, 70), (14, 61), (15, 89), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106da6) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106d50_1 code

theorem block_l106d50 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106d50 :=
  Rest.liftedBlock (rest_l106d50 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106d50 x hx)

theorem rest_l106ebc_3 [Bindings] (code : CodeMap) :
    Rest (n := 166) code lifted (codeRange 0x106ebc bytes_l106ebc) [(0, 0), (1, 164), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x106fa0 bytes_l106ebc_3 b_l106ebc_3 := by
  have f60 : InstrSpec 0x106fa0 [0x31, 0xC8] (fun s => s.RIP = 0x106fa0) (xorR32R32Effect 0x106fa0 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106fa0 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x106fa0 0xc8 (by decide)) pre_rip
  have f61 : InstrSpec 0x106fa2 [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106fa2) (shlR32Effect 0x106fa2 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x106fa2 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x106fa2 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x106fa5 [0x31, 0xC1] (fun s => s.RIP = 0x106fa5) (xorR32R32Effect 0x106fa5 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106fa5 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106fa5 0xc1 (by decide)) pre_rip
  have f63 : InstrSpec 0x106fa7 [0x66, 0x89, 0x4C, 0x24, 0x16] (StorePre 0x106fa7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106fa7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106fa7 5 1 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106fa7 5 1 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m16_r16_effect_step 0x106fa7 1 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f64 : InstrSpec 0x106fac [0x4C, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x106fac) (leaR64Effect 0x106fac 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x106fac 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x106fac 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x106fb1 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x106fb1) (movR32Imm32Effect 0x106fb1 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x106fb1 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x106fb1 0xbe (by decide) 0x8) pre_rip
  have f66 : InstrSpec 0x106fb6 [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x106fb6) (movR64R64Effect 0x106fb6 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x106fb6 7 15).toInstrSpec (mov_r64_r64_effect_step 0x106fb6 0x4c 0xff (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x106fb9 [0xE8, 0x52, 0x9B, 0xFF, 0xFF] (PushPre 0x106fb9 5) (callEffect (fun _ => 0x100b10) 0x106fbe)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x106fb9 0x100b10 0x106fbe).toInstrSpec (call_rel32_effect_step 0x106fb9 0xffff9b52 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 166), (1, 164), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fa2) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f61 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 166), (1, 168), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fa5) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f62 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fa7) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.exec (n := 172) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fac) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f64 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (15, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fb1) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f65 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 4), (5, 5), (6, 175), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (15, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fb6) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f66 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 4), (5, 5), (6, 175), (7, 177), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (15, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fb9) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f67 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 179), (5, 5), (6, 175), (7, 177), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (15, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f67 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 181) (by decide) (by decide) rfl rfl

theorem rest_l106ebc_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x106ebc bytes_l106ebc) [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 121), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      28 0x106f5e bytes_l106ebc_2 b_l106ebc_2 := by
  have f40 : InstrSpec 0x106f5e [0x0F, 0xB7, 0xF2] (fun s => s.RIP = 0x106f5e) (movzxR32R16Effect 0x106f5e 3 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movzxR32R16Effect_footprint 0x106f5e 3 6 2).toInstrSpec (movzx_r32_r16_effect_step 0x106f5e 0xf2 (by decide)) pre_rip
  have f41 : InstrSpec 0x106f61 [0xC1, 0xEE, 0x02] (fun s => s.RIP = 0x106f61) (shrR32Effect 0x106f61 3 6 2)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x106f61 3 6 2).toInstrSpec (shr_r32_imm8_effect_step 0x106f61 0xee 0x2 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x106f64 [0x31, 0xD6] (fun s => s.RIP = 0x106f64) (xorR32R32Effect 0x106f64 2 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f64 2 6 2).toInstrSpec (xor_r32_r32_effect_step 0x106f64 0xd6 (by decide)) pre_rip
  have f43 : InstrSpec 0x106f66 [0x81, 0xE6, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106f66) (andR32Imm32Effect 0x106f66 6 6 0x3030)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106f66 6 6 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x106f66 0xe6 0x3030 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x106f6c [0x31, 0xF2] (fun s => s.RIP = 0x106f6c) (xorR32R32Effect 0x106f6c 2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f6c 2 2 6).toInstrSpec (xor_r32_r32_effect_step 0x106f6c 0xf2 (by decide)) pre_rip
  have f45 : InstrSpec 0x106f6e [0xC1, 0xE6, 0x02] (fun s => s.RIP = 0x106f6e) (shlR32Effect 0x106f6e 3 6 2)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR32Effect_footprint 0x106f6e 3 6 2).toInstrSpec (shl_r32_imm8_effect_step 0x106f6e 0xe6 0x2 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x106f71 [0x31, 0xD6] (fun s => s.RIP = 0x106f71) (xorR32R32Effect 0x106f71 2 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f71 2 6 2).toInstrSpec (xor_r32_r32_effect_step 0x106f71 0xd6 (by decide)) pre_rip
  have f47 : InstrSpec 0x106f73 [0x66, 0x89, 0x74, 0x24, 0x12] (StorePre 0x106f73 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106f73 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106f73 5 6 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106f73 5 6 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (mov_m16_r16_effect_step 0x106f73 6 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x106f78 [0x0F, 0xB7, 0xD1] (fun s => s.RIP = 0x106f78) (movzxR32R16Effect 0x106f78 3 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movzxR32R16Effect_footprint 0x106f78 3 2 1).toInstrSpec (movzx_r32_r16_effect_step 0x106f78 0xd1 (by decide)) pre_rip
  have f49 : InstrSpec 0x106f7b [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x106f7b) (shrR32Effect 0x106f7b 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x106f7b 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x106f7b 0xea 0x2 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x106f7e [0x31, 0xCA] (fun s => s.RIP = 0x106f7e) (xorR32R32Effect 0x106f7e 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f7e 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x106f7e 0xca (by decide)) pre_rip
  have f51 : InstrSpec 0x106f80 [0x81, 0xE2, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106f80) (andR32Imm32Effect 0x106f80 6 2 0x3030)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106f80 6 2 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x106f80 0xe2 0x3030 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x106f86 [0x31, 0xD1] (fun s => s.RIP = 0x106f86) (xorR32R32Effect 0x106f86 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f86 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x106f86 0xd1 (by decide)) pre_rip
  have f53 : InstrSpec 0x106f88 [0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x106f88) (shlR32Effect 0x106f88 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x106f88 3 2 2).toInstrSpec (shl_r32_imm8_effect_step 0x106f88 0xe2 0x2 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x106f8b [0x31, 0xCA] (fun s => s.RIP = 0x106f8b) (xorR32R32Effect 0x106f8b 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f8b 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x106f8b 0xca (by decide)) pre_rip
  have f55 : InstrSpec 0x106f8d [0x66, 0x89, 0x54, 0x24, 0x14] (StorePre 0x106f8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106f8d + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106f8d 5 2 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106f8d 5 2 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m16_r16_effect_step 0x106f8d 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x106f92 [0x0F, 0xB7, 0xC8] (fun s => s.RIP = 0x106f92) (movzxR32R16Effect 0x106f92 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R16Effect_footprint 0x106f92 3 1 0).toInstrSpec (movzx_r32_r16_effect_step 0x106f92 0xc8 (by decide)) pre_rip
  have f57 : InstrSpec 0x106f95 [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106f95) (shrR32Effect 0x106f95 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x106f95 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x106f95 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x106f98 [0x31, 0xC1] (fun s => s.RIP = 0x106f98) (xorR32R32Effect 0x106f98 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f98 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x106f98 0xc1 (by decide)) pre_rip
  have f59 : InstrSpec 0x106f9a [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106f9a) (andR32Imm32Effect 0x106f9a 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106f9a 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x106f9a 0xe1 0x3030 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 128), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f61) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f41 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 130), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f64) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 132), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f66) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 134), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f6c) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 0), (1, 1), (2, 136), (3, 3), (4, 4), (5, 5), (6, 134), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f6e) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 0), (1, 1), (2, 136), (3, 3), (4, 4), (5, 5), (6, 138), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f71) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f46 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 0), (1, 1), (2, 136), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f73) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.exec (n := 142) (ρ' := [(0, 0), (1, 1), (2, 136), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f78) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 0), (1, 1), (2, 143), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f7b) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f49 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 0), (1, 1), (2, 145), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f7e) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 0), (1, 1), (2, 147), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f80) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f51 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 0), (1, 1), (2, 149), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f86) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f52 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 0), (1, 151), (2, 149), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f88) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 0), (1, 151), (2, 153), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f8b) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f54 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 0), (1, 151), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f8d) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.exec (n := 157) (ρ' := [(0, 0), (1, 151), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f92) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f56 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 0), (1, 158), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f95) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f57 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 0), (1, 160), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f98) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 0), (1, 162), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f9a) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 0), (1, 164), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fa0) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106ebc_3 code

theorem rest_l106ebc_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x106ebc bytes_l106ebc) [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 89), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      48 0x106f12 bytes_l106ebc_1 b_l106ebc_1 := by
  have f20 : InstrSpec 0x106f12 [0x45, 0x31, 0xC8] (fun s => s.RIP = 0x106f12) (xorR32R32Effect 0x106f12 3 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f12 3 8 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x106f12 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x106f15 [0x41, 0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x106f15) (shlR32Effect 0x106f15 4 9 2)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR32Effect_footprint 0x106f15 4 9 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x106f15 0x41 0xe1 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x106f19 [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x106f19) (xorR32R32Effect 0x106f19 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f19 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x106f19 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x106f1c [0x66, 0x44, 0x89, 0x4C, 0x24, 0x0C] (StorePre 0x106f1c 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106f1c + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106f1c 6 9 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106f1c 6 9 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106f1c 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x106f22 [0x44, 0x0F, 0xB7, 0xC7] (fun s => s.RIP = 0x106f22) (movzxR32R16Effect 0x106f22 4 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movzxR32R16Effect_footprint 0x106f22 4 8 7).toInstrSpec (movzx_r32_r16_rex_effect_step 0x106f22 0x44 (by decide) 0xc7 (by decide)) pre_rip
  have f25 : InstrSpec 0x106f26 [0x41, 0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x106f26) (shrR32Effect 0x106f26 4 8 2)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x106f26 4 8 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x106f26 0x41 0xe8 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x106f2a [0x41, 0x31, 0xF8] (fun s => s.RIP = 0x106f2a) (xorR32R32Effect 0x106f2a 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f2a 3 8 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x106f2a 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x106f2d [0x41, 0x81, 0xE0, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106f2d) (andR32Imm32Effect 0x106f2d 7 8 0x3030)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106f2d 7 8 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x106f2d 0x41 0xe0 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x106f34 [0x44, 0x31, 0xC7] (fun s => s.RIP = 0x106f34) (xorR32R32Effect 0x106f34 3 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f34 3 7 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x106f34 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x106f37 [0x41, 0xC1, 0xE0, 0x02] (fun s => s.RIP = 0x106f37) (shlR32Effect 0x106f37 4 8 2)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR32Effect_footprint 0x106f37 4 8 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x106f37 0x41 0xe0 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x106f3b [0x41, 0x31, 0xF8] (fun s => s.RIP = 0x106f3b) (xorR32R32Effect 0x106f3b 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f3b 3 8 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x106f3b 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x106f3e [0x66, 0x44, 0x89, 0x44, 0x24, 0x0E] (StorePre 0x106f3e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106f3e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106f3e 6 8 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106f3e 6 8 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106f3e 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x106f44 [0x0F, 0xB7, 0xFE] (fun s => s.RIP = 0x106f44) (movzxR32R16Effect 0x106f44 3 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movzxR32R16Effect_footprint 0x106f44 3 7 6).toInstrSpec (movzx_r32_r16_effect_step 0x106f44 0xfe (by decide)) pre_rip
  have f33 : InstrSpec 0x106f47 [0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x106f47) (shrR32Effect 0x106f47 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x106f47 3 7 2).toInstrSpec (shr_r32_imm8_effect_step 0x106f47 0xef 0x2 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x106f4a [0x31, 0xF7] (fun s => s.RIP = 0x106f4a) (xorR32R32Effect 0x106f4a 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f4a 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x106f4a 0xf7 (by decide)) pre_rip
  have f35 : InstrSpec 0x106f4c [0x81, 0xE7, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106f4c) (andR32Imm32Effect 0x106f4c 6 7 0x3030)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106f4c 6 7 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x106f4c 0xe7 0x3030 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x106f52 [0x31, 0xFE] (fun s => s.RIP = 0x106f52) (xorR32R32Effect 0x106f52 2 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f52 2 6 7).toInstrSpec (xor_r32_r32_effect_step 0x106f52 0xfe (by decide)) pre_rip
  have f37 : InstrSpec 0x106f54 [0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x106f54) (shlR32Effect 0x106f54 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x106f54 3 7 2).toInstrSpec (shl_r32_imm8_effect_step 0x106f54 0xe7 0x2 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x106f57 [0x31, 0xF7] (fun s => s.RIP = 0x106f57) (xorR32R32Effect 0x106f57 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f57 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x106f57 0xf7 (by decide)) pre_rip
  have f39 : InstrSpec 0x106f59 [0x66, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x106f59 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106f59 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106f59 5 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106f59 5 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m16_r16_effect_step 0x106f59 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 91), (9, 89), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f15) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 91), (9, 93), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f19) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 91), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f1c) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 91), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f22) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 98), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f26) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 100), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f2a) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 102), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f2d) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 104), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f34) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 106), (8, 104), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f37) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 106), (8, 108), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f3b) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 106), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f3e) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 106), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f44) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 113), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f47) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 115), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f4a) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 117), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f4c) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 119), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f52) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 121), (7, 119), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f54) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 121), (7, 123), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f57) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 121), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f59) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.exec (n := 127) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 121), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f5e) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l106ebc_2 code

theorem rest_l106ebc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106ebc bytes_l106ebc) (entryMap (live .l106ebc))
      68 0x106ebc bytes_l106ebc b_l106ebc := by
  have f0 : InstrSpec 0x106ebc [0x45, 0x0F, 0xB7, 0xDA] (fun s => s.RIP = 0x106ebc) (movzxR32R16Effect 0x106ebc 4 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movzxR32R16Effect_footprint 0x106ebc 4 11 10).toInstrSpec (movzx_r32_r16_rex_effect_step 0x106ebc 0x45 (by decide) 0xda (by decide)) pre_rip
  have f1 : InstrSpec 0x106ec0 [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x106ec0) (shrR32Effect 0x106ec0 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x106ec0 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x106ec0 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x106ec4 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x106ec4) (xorR32R32Effect 0x106ec4 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106ec4 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x106ec4 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x106ec7 [0x41, 0x81, 0xE3, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106ec7) (andR32Imm32Effect 0x106ec7 7 11 0x3030)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106ec7 7 11 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x106ec7 0x41 0xe3 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x106ece [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x106ece) (xorR32R32Effect 0x106ece 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106ece 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x106ece 0x45 0xda (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x106ed1 [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x106ed1) (shlR32Effect 0x106ed1 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x106ed1 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x106ed1 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x106ed5 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x106ed5) (xorR32R32Effect 0x106ed5 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106ed5 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x106ed5 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x106ed8 [0x66, 0x44, 0x89, 0x5C, 0x24, 0x08] (StorePre 0x106ed8 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106ed8 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106ed8 6 11 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106ed8 6 11 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106ed8 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x106ede [0x45, 0x0F, 0xB7, 0xD1] (fun s => s.RIP = 0x106ede) (movzxR32R16Effect 0x106ede 4 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movzxR32R16Effect_footprint 0x106ede 4 10 9).toInstrSpec (movzx_r32_r16_rex_effect_step 0x106ede 0x45 (by decide) 0xd1 (by decide)) pre_rip
  have f9 : InstrSpec 0x106ee2 [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x106ee2) (shrR32Effect 0x106ee2 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x106ee2 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x106ee2 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x106ee6 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x106ee6) (xorR32R32Effect 0x106ee6 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106ee6 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x106ee6 0x45 0xca (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x106ee9 [0x41, 0x81, 0xE2, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106ee9) (andR32Imm32Effect 0x106ee9 7 10 0x3030)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106ee9 7 10 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x106ee9 0x41 0xe2 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x106ef0 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x106ef0) (xorR32R32Effect 0x106ef0 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106ef0 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x106ef0 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x106ef3 [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x106ef3) (shlR32Effect 0x106ef3 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x106ef3 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x106ef3 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x106ef7 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x106ef7) (xorR32R32Effect 0x106ef7 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106ef7 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x106ef7 0x45 0xca (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x106efa [0x66, 0x44, 0x89, 0x54, 0x24, 0x0A] (StorePre 0x106efa 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106efa + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106efa 6 10 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x106efa 6 10 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m16_r16_rex_effect_step 0x106efa 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x106f00 [0x45, 0x0F, 0xB7, 0xC8] (fun s => s.RIP = 0x106f00) (movzxR32R16Effect 0x106f00 4 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movzxR32R16Effect_footprint 0x106f00 4 9 8).toInstrSpec (movzx_r32_r16_rex_effect_step 0x106f00 0x45 (by decide) 0xc8 (by decide)) pre_rip
  have f17 : InstrSpec 0x106f04 [0x41, 0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x106f04) (shrR32Effect 0x106f04 4 9 2)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x106f04 4 9 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x106f04 0x41 0xe9 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x106f08 [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x106f08) (xorR32R32Effect 0x106f08 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x106f08 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x106f08 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x106f0b [0x41, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x106f0b) (andR32Imm32Effect 0x106f0b 7 9 0x3030)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x106f0b 7 9 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x106f0b 0x41 0xe1 0x3030 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ec0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ec4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ec7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ece) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 59), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ed1) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 63), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ed5) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ed8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ede) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 68), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ee2) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 70), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ee6) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 72), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ee9) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 74), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ef0) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 76), (10, 74), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ef3) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 76), (10, 78), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ef7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 76), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106efa) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 76), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f00) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 83), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f04) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 85), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f08) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 87), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f0b) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 89), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106f12) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106ebc_1 code

theorem block_l106ebc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106ebc :=
  Rest.liftedBlock (rest_l106ebc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106ebc x hx)

theorem rest_l106fbe_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x106fbe bytes_l106fbe) [(0, 76), (1, 53), (2, 79), (3, 81), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x107030 bytes_l106fbe_1 b_l106fbe_1 := by
  have f20 : InstrSpec 0x107030 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x107030) (movR64R64Effect 0x107030 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x107030 6 15).toInstrSpec (mov_r64_r64_effect_step 0x107030 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x107033 [0xE8, 0x58, 0x2D, 0x00, 0x00] (PushPre 0x107033 5) (callEffect (fun _ => 0x109d90) 0x107038)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x107033 0x109d90 0x107038).toInstrSpec (call_rel32_effect_step 0x107033 0x2d58 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 76), (1, 53), (2, 79), (3, 81), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107033) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 76), (1, 53), (2, 79), (3, 81), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d90) f21 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem rest_l106fbe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x106fbe bytes_l106fbe) (entryMap (live .l106fbe))
      22 0x106fbe bytes_l106fbe b_l106fbe := by
  have f0 : InstrSpec 0x106fbe [0x48, 0x8B, 0x4C, 0x24, 0x30] (LoadPre 0x106fbe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106fbe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106fbe 1 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x106fbe 1 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x106fbe 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x106fc3 [0x0F, 0xB7, 0x81, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x106fc3 (fun s => AddrMode.addr (.base 1 (.d32 0xe0)) s (0x106fc3 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106fc3 7 0 (.base 1 (.d32 0xe0)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106fc3 7 0 (.base 1 (.d32 0xe0))).toInstrSpec (movzx_r32_m16_effect_step 0x106fc3 0 (.base 1 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x106fca [0x66, 0x31, 0x44, 0x24, 0x08] (StorePre 0x106fca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106fca + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106fca 5 16 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106fca 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m16_r16_effect_step 0x106fca 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x106fcf [0x0F, 0xB7, 0x81, 0xE2, 0x00, 0x00, 0x00] (LoadPre 0x106fcf (fun s => AddrMode.addr (.base 1 (.d32 0xe2)) s (0x106fcf + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106fcf 7 0 (.base 1 (.d32 0xe2)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106fcf 7 0 (.base 1 (.d32 0xe2))).toInstrSpec (movzx_r32_m16_effect_step 0x106fcf 0 (.base 1 (.d32 0xe2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x106fd6 [0x66, 0x31, 0x44, 0x24, 0x0A] (StorePre 0x106fd6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106fd6 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106fd6 5 16 0 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106fd6 5 0 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (xor_m16_r16_effect_step 0x106fd6 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x106fdb [0x0F, 0xB7, 0x81, 0xE4, 0x00, 0x00, 0x00] (LoadPre 0x106fdb (fun s => AddrMode.addr (.base 1 (.d32 0xe4)) s (0x106fdb + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106fdb 7 0 (.base 1 (.d32 0xe4)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106fdb 7 0 (.base 1 (.d32 0xe4))).toInstrSpec (movzx_r32_m16_effect_step 0x106fdb 0 (.base 1 (.d32 0xe4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x106fe2 [0x66, 0x31, 0x44, 0x24, 0x0C] (StorePre 0x106fe2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106fe2 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106fe2 5 16 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106fe2 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (xor_m16_r16_effect_step 0x106fe2 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x106fe7 [0x0F, 0xB7, 0x81, 0xE6, 0x00, 0x00, 0x00] (LoadPre 0x106fe7 (fun s => AddrMode.addr (.base 1 (.d32 0xe6)) s (0x106fe7 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106fe7 7 0 (.base 1 (.d32 0xe6)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106fe7 7 0 (.base 1 (.d32 0xe6))).toInstrSpec (movzx_r32_m16_effect_step 0x106fe7 0 (.base 1 (.d32 0xe6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x106fee [0x66, 0x31, 0x44, 0x24, 0x0E] (StorePre 0x106fee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106fee + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106fee 5 16 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106fee 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (xor_m16_r16_effect_step 0x106fee 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x106ff3 [0x0F, 0xB7, 0x81, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x106ff3 (fun s => AddrMode.addr (.base 1 (.d32 0xe8)) s (0x106ff3 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106ff3 7 0 (.base 1 (.d32 0xe8)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106ff3 7 0 (.base 1 (.d32 0xe8))).toInstrSpec (movzx_r32_m16_effect_step 0x106ff3 0 (.base 1 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x106ffa [0x66, 0x31, 0x44, 0x24, 0x10] (StorePre 0x106ffa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106ffa + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106ffa 5 16 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x106ffa 5 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (xor_m16_r16_effect_step 0x106ffa 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x106fff [0x0F, 0xB7, 0x81, 0xEA, 0x00, 0x00, 0x00] (LoadPre 0x106fff (fun s => AddrMode.addr (.base 1 (.d32 0xea)) s (0x106fff + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106fff 7 0 (.base 1 (.d32 0xea)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x106fff 7 0 (.base 1 (.d32 0xea))).toInstrSpec (movzx_r32_m16_effect_step 0x106fff 0 (.base 1 (.d32 0xea)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x107006 [0x66, 0x31, 0x44, 0x24, 0x12] (StorePre 0x107006 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x107006 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x107006 5 16 0 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x107006 5 0 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (xor_m16_r16_effect_step 0x107006 0 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10700b [0x0F, 0xB7, 0x81, 0xEC, 0x00, 0x00, 0x00] (LoadPre 0x10700b (fun s => AddrMode.addr (.base 1 (.d32 0xec)) s (0x10700b + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x10700b 7 0 (.base 1 (.d32 0xec)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10700b 7 0 (.base 1 (.d32 0xec))).toInstrSpec (movzx_r32_m16_effect_step 0x10700b 0 (.base 1 (.d32 0xec)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x107012 [0x66, 0x31, 0x44, 0x24, 0x14] (StorePre 0x107012 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x107012 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x107012 5 16 0 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x107012 5 0 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (xor_m16_r16_effect_step 0x107012 0 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x107017 [0x0F, 0xB7, 0x81, 0xEE, 0x00, 0x00, 0x00] (LoadPre 0x107017 (fun s => AddrMode.addr (.base 1 (.d32 0xee)) s (0x107017 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x107017 7 0 (.base 1 (.d32 0xee)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x107017 7 0 (.base 1 (.d32 0xee))).toInstrSpec (movzx_r32_m16_effect_step 0x107017 0 (.base 1 (.d32 0xee)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10701e [0x66, 0x31, 0x44, 0x24, 0x16] (StorePre 0x10701e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x10701e + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10701e 5 16 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x10701e 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (xor_m16_r16_effect_step 0x10701e 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x107023 [0xBA, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x107023) (movR32Imm32Effect 0x107023 5 2 0x8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x107023 5 2 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x107023 0xba (by decide) 0x8) pre_rip
  have f18 : InstrSpec 0x107028 [0x48, 0x8B, 0x5C, 0x24, 0x40] (LoadPre 0x107028 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107028 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107028 3 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x107028 3 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x107028 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10702d [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x10702d) (movR64R64Effect 0x10702d 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10702d 7 3).toInstrSpec (mov_r64_r64_effect_step 0x10702d 0x48 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fc3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fcf) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fd6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fdb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fe2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fe7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fee) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ff3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106ffa) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x106fff) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107006) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 70), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10700b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107012) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107017) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10701e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107023) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 76), (1, 53), (2, 79), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107028) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 76), (1, 53), (2, 79), (3, 81), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10702d) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 76), (1, 53), (2, 79), (3, 81), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107030) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l106fbe_1 code

theorem block_l106fbe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l106fbe :=
  Rest.liftedBlock (rest_l106fbe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l106fbe x hx)

theorem rest_l107038 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x107038 bytes_l107038) (entryMap (live .l107038))
      9 0x107038 bytes_l107038 b_l107038 := by
  have f0 : InstrSpec 0x107038 [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x107038) (movR64R64Effect 0x107038 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x107038 0 3).toInstrSpec (mov_r64_r64_effect_step 0x107038 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10703b [0x48, 0x83, 0xC4, 0x48] (fun s => s.RIP = 0x10703b) (addR64Imm8Effect 0x10703b 4 0x48)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10703b 4 0x48).toInstrSpec (add_r64_imm8_effect_step 0x10703b 0x48 0xc4 0x48 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10703f [0x5B] (PopPre 0x10703f) (popR64Effect 0x10703f 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10703f 1 3).toInstrSpec (pop_r64_effect_step 0x10703f 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x107040 [0x41, 0x5C] (PopPre 0x107040) (popR64Effect 0x107040 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107040 2 12).toInstrSpec (pop_r64_rex_effect_step 0x107040 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x107042 [0x41, 0x5D] (PopPre 0x107042) (popR64Effect 0x107042 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107042 2 13).toInstrSpec (pop_r64_rex_effect_step 0x107042 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x107044 [0x41, 0x5E] (PopPre 0x107044) (popR64Effect 0x107044 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107044 2 14).toInstrSpec (pop_r64_rex_effect_step 0x107044 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x107046 [0x41, 0x5F] (PopPre 0x107046) (popR64Effect 0x107046 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107046 2 15).toInstrSpec (pop_r64_rex_effect_step 0x107046 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x107048 [0x5D] (PopPre 0x107048) (popR64Effect 0x107048 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x107048 1 5).toInstrSpec (pop_r64_effect_step 0x107048 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x107049 [0xC3] (RetPre 0x107049) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x107049).toInstrSpec (ret_effect_step 0x107049) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10703b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10703f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107040) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107042) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107044) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107046) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107048) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x107049) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l107038 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l107038 :=
  Rest.liftedBlock (rest_l107038 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l107038 x hx)

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

theorem_by block_l106960_eval :
    program.runBlock (dialect code) ⟨.l106960, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106997_eval :
    program.runBlock (dialect code) ⟨.l106997, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1069f0_eval :
    program.runBlock (dialect code) ⟨.l1069f0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a11_eval :
    program.runBlock (dialect code) ⟨.l106a11, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106a19_eval :
    program.runBlock (dialect code) ⟨.l106a19, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106aa9_eval :
    program.runBlock (dialect code) ⟨.l106aa9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106ab8_eval :
    program.runBlock (dialect code) ⟨.l106ab8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106ce3_eval :
    program.runBlock (dialect code) ⟨.l106ce3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106ceb_eval :
    program.runBlock (dialect code) ⟨.l106ceb, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106d50_eval :
    program.runBlock (dialect code) ⟨.l106d50, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106ebc_eval :
    program.runBlock (dialect code) ⟨.l106ebc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l106fbe_eval :
    program.runBlock (dialect code) ⟨.l106fbe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l107038_eval :
    program.runBlock (dialect code) ⟨.l107038, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
