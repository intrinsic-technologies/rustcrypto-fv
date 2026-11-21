import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l109ff0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109ff0 bytes_l109ff0) (entryMap (live .l109ff0))
      9 0x109ff0 bytes_l109ff0 b_l109ff0 := by
  have f0 : InstrSpec 0x109ff0 [0x55] (PushPre 0x109ff0 1) (pushR64Effect 0x109ff0 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109ff0 1 5).toInstrSpec (push_r64_effect_step 0x109ff0 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x109ff1 [0x41, 0x57] (PushPre 0x109ff1 2) (pushR64Effect 0x109ff1 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109ff1 2 15).toInstrSpec (push_r64_rex_effect_step 0x109ff1 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109ff3 [0x41, 0x56] (PushPre 0x109ff3 2) (pushR64Effect 0x109ff3 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109ff3 2 14).toInstrSpec (push_r64_rex_effect_step 0x109ff3 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109ff5 [0x41, 0x55] (PushPre 0x109ff5 2) (pushR64Effect 0x109ff5 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109ff5 2 13).toInstrSpec (push_r64_rex_effect_step 0x109ff5 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x109ff7 [0x41, 0x54] (PushPre 0x109ff7 2) (pushR64Effect 0x109ff7 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109ff7 2 12).toInstrSpec (push_r64_rex_effect_step 0x109ff7 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x109ff9 [0x53] (PushPre 0x109ff9 1) (pushR64Effect 0x109ff9 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109ff9 1 3).toInstrSpec (push_r64_effect_step 0x109ff9 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x109ffa [0x48, 0x83, 0xEC, 0x18] (fun s => s.RIP = 0x109ffa) (subR64Imm8Effect 0x109ffa 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x109ffa 4 0x18).toInstrSpec (sub_r64_imm8_effect_step 0x109ffa 0x48 0xec 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x109ffe [0x48, 0x83, 0xFE, 0x07] (fun s => s.RIP = 0x109ffe) (cmpR64Imm8Effect 0x109ffe 6 0x7)
      [.gpr 6] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x109ffe 6 0x7).toInstrSpec (cmp_r64_imm8_effect_step 0x109ffe 0x48 0xfe 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff5) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ffa) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ffe) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f7 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 67), (19, 68), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a002) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 70) (jcc_rel32_effect_step 0x10a002 6 0x1e9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109ff0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109ff0 :=
  Rest.liftedBlock (rest_l109ff0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109ff0 x hx)

theorem rest_l10a008_6 [Bindings] (code : CodeMap) :
    Rest (n := 291) code lifted (codeRange 0x10a008 bytes_l10a008) [(0, 285), (1, 289), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]
      19 0x10a1b5 bytes_l10a008_6 b_l10a008_6 := by
  have f120 : InstrSpec 0x10a1b5 [0x44, 0x31, 0xD9] (fun s => s.RIP = 0x10a1b5) (xorR32R32Effect 0x10a1b5 3 1 11)
      [.gpr 1, .gpr 11] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a1b5 3 1 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a1b5 0x44 0xd9 (by decide) (by decide)) pre_rip
  have f121 : InstrSpec 0x10a1b8 [0x44, 0x31, 0xF8] (fun s => s.RIP = 0x10a1b8) (xorR32R32Effect 0x10a1b8 3 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a1b8 3 0 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a1b8 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x10a1bb [0x48, 0x8B, 0x74, 0x24, 0x10] (LoadPre 0x10a1bb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a1bb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a1bb 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x10a1bb 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x10a1bb 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f123 : InstrSpec 0x10a1c0 [0x66, 0x89, 0x0E] (StorePre 0x10a1c0 3 (fun s => AddrMode.addr (.base 6 .none) s (0x10a1c0 + BitVec.ofNat 64 3)) 2) (movM16R16Effect 0x10a1c0 3 1 (.base 6 .none))
      [.gpr 1, .gpr 6] [] [.rip] :=
    (movM16R16Effect_footprint 0x10a1c0 3 1 (.base 6 .none)).toInstrSpec (mov_m16_r16_effect_step 0x10a1c0 1 (.base 6 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f124 : InstrSpec 0x10a1c3 [0x66, 0x44, 0x89, 0x56, 0x02] (StorePre 0x10a1c3 5 (fun s => AddrMode.addr (.base 6 (.d8 0x2)) s (0x10a1c3 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10a1c3 5 10 (.base 6 (.d8 0x2)))
      [.gpr 10, .gpr 6] [] [.rip] :=
    (movM16R16Effect_footprint 0x10a1c3 5 10 (.base 6 (.d8 0x2))).toInstrSpec (mov_m16_r16_rex_effect_step 0x10a1c3 0x44 (by decide) 2 (.base 6 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f125 : InstrSpec 0x10a1c8 [0x66, 0x89, 0x7E, 0x04] (StorePre 0x10a1c8 4 (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x10a1c8 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10a1c8 4 7 (.base 6 (.d8 0x4)))
      [.gpr 7, .gpr 6] [] [.rip] :=
    (movM16R16Effect_footprint 0x10a1c8 4 7 (.base 6 (.d8 0x4))).toInstrSpec (mov_m16_r16_effect_step 0x10a1c8 7 (.base 6 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f126 : InstrSpec 0x10a1cc [0x66, 0x89, 0x56, 0x06] (StorePre 0x10a1cc 4 (fun s => AddrMode.addr (.base 6 (.d8 0x6)) s (0x10a1cc + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10a1cc 4 2 (.base 6 (.d8 0x6)))
      [.gpr 2, .gpr 6] [] [.rip] :=
    (movM16R16Effect_footprint 0x10a1cc 4 2 (.base 6 (.d8 0x6))).toInstrSpec (mov_m16_r16_effect_step 0x10a1cc 2 (.base 6 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f127 : InstrSpec 0x10a1d0 [0x66, 0x89, 0x46, 0x08] (StorePre 0x10a1d0 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a1d0 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10a1d0 4 0 (.base 6 (.d8 0x8)))
      [.gpr 0, .gpr 6] [] [.rip] :=
    (movM16R16Effect_footprint 0x10a1d0 4 0 (.base 6 (.d8 0x8))).toInstrSpec (mov_m16_r16_effect_step 0x10a1d0 0 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f128 : InstrSpec 0x10a1d4 [0x66, 0x44, 0x89, 0x46, 0x0A] (StorePre 0x10a1d4 5 (fun s => AddrMode.addr (.base 6 (.d8 0xa)) s (0x10a1d4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10a1d4 5 8 (.base 6 (.d8 0xa)))
      [.gpr 8, .gpr 6] [] [.rip] :=
    (movM16R16Effect_footprint 0x10a1d4 5 8 (.base 6 (.d8 0xa))).toInstrSpec (mov_m16_r16_rex_effect_step 0x10a1d4 0x44 (by decide) 0 (.base 6 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f129 : InstrSpec 0x10a1d9 [0x66, 0x89, 0x6E, 0x0C] (StorePre 0x10a1d9 4 (fun s => AddrMode.addr (.base 6 (.d8 0xc)) s (0x10a1d9 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x10a1d9 4 5 (.base 6 (.d8 0xc)))
      [.gpr 5, .gpr 6] [] [.rip] :=
    (movM16R16Effect_footprint 0x10a1d9 4 5 (.base 6 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x10a1d9 5 (.base 6 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f130 : InstrSpec 0x10a1dd [0x66, 0x44, 0x89, 0x66, 0x0E] (StorePre 0x10a1dd 5 (fun s => AddrMode.addr (.base 6 (.d8 0xe)) s (0x10a1dd + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10a1dd 5 12 (.base 6 (.d8 0xe)))
      [.gpr 12, .gpr 6] [] [.rip] :=
    (movM16R16Effect_footprint 0x10a1dd 5 12 (.base 6 (.d8 0xe))).toInstrSpec (mov_m16_r16_rex_effect_step 0x10a1dd 0x44 (by decide) 4 (.base 6 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f131 : InstrSpec 0x10a1e2 [0x48, 0x83, 0xC4, 0x18] (fun s => s.RIP = 0x10a1e2) (addR64Imm8Effect 0x10a1e2 4 0x18)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10a1e2 4 0x18).toInstrSpec (add_r64_imm8_effect_step 0x10a1e2 0x48 0xc4 0x18 (by decide) (by decide) (by decide)) pre_rip
  have f132 : InstrSpec 0x10a1e6 [0x5B] (PopPre 0x10a1e6) (popR64Effect 0x10a1e6 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a1e6 1 3).toInstrSpec (pop_r64_effect_step 0x10a1e6 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f133 : InstrSpec 0x10a1e7 [0x41, 0x5C] (PopPre 0x10a1e7) (popR64Effect 0x10a1e7 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a1e7 2 12).toInstrSpec (pop_r64_rex_effect_step 0x10a1e7 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f134 : InstrSpec 0x10a1e9 [0x41, 0x5D] (PopPre 0x10a1e9) (popR64Effect 0x10a1e9 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a1e9 2 13).toInstrSpec (pop_r64_rex_effect_step 0x10a1e9 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f135 : InstrSpec 0x10a1eb [0x41, 0x5E] (PopPre 0x10a1eb) (popR64Effect 0x10a1eb 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a1eb 2 14).toInstrSpec (pop_r64_rex_effect_step 0x10a1eb 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f136 : InstrSpec 0x10a1ed [0x41, 0x5F] (PopPre 0x10a1ed) (popR64Effect 0x10a1ed 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a1ed 2 15).toInstrSpec (pop_r64_rex_effect_step 0x10a1ed 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f137 : InstrSpec 0x10a1ef [0x5D] (PopPre 0x10a1ef) (popR64Effect 0x10a1ef 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10a1ef 1 5).toInstrSpec (pop_r64_effect_step 0x10a1ef 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f138 : InstrSpec 0x10a1f0 [0xC3] (RetPre 0x10a1f0) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10a1f0).toInstrSpec (ret_effect_step 0x10a1f0) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f120 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 285), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1b8) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f121 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1bb) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f122 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1c0) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.exec (n := 297) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1c3) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 298) (RestInside.exec (n := 298) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1c8) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 299) (RestInside.exec (n := 299) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1cc) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 300) (RestInside.exec (n := 300) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1d0) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 301) (RestInside.exec (n := 301) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1d4) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 302) (RestInside.exec (n := 302) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1d9) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 303) (RestInside.exec (n := 303) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1dd) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 304) (RestInside.exec (n := 304) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 4), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1e2) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 305) (RestInside.out (n := 305) f131 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 306) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 197), (4, 305), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1e6) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 307) (RestInside.out (n := 307) f132 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 308) f132 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 309) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 307), (4, 308), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1e7) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 310) (RestInside.out (n := 310) f133 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 311) f133 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 312) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 307), (4, 311), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 310), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1e9) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f134 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 314) f134 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 315) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 307), (4, 314), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 310), (13, 313), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1eb) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 316) (RestInside.out (n := 316) f135 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 317) f135 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 318) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 307), (4, 317), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 310), (13, 313), (14, 316), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1ed) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 319) (RestInside.out (n := 319) f136 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 320) f136 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 321) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 307), (4, 320), (5, 245), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 310), (13, 313), (14, 316), (15, 319), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1ef) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 322) (RestInside.out (n := 322) f137 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 323) f137 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 324) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 307), (4, 323), (5, 322), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 310), (13, 313), (14, 316), (15, 319), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1f0) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 325) (RestInside.out (n := 325) f138 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 326) f138 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 327) (ρ' := [(0, 293), (1, 291), (2, 189), (3, 307), (4, 326), (5, 322), (6, 295), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 310), (13, 313), (14, 316), (15, 319), (22, 22), (39, 39), (50, 50), (51, 51)]) f138 (by decide) rfl rfl rfl (by decide)

theorem rest_l10a008_5 [Bindings] (code : CodeMap) :
    Rest (n := 251) code lifted (codeRange 0x10a008 bytes_l10a008) [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]
      39 0x10a16f bytes_l10a008_5 b_l10a008_5 := by
  have f100 : InstrSpec 0x10a16f [0x41, 0x89, 0xF0] (fun s => s.RIP = 0x10a16f) (movR32R32Effect 0x10a16f 3 8 6)
      [.gpr 6] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x10a16f 3 8 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a16f 0x41 0xf0 (by decide) (by decide)) pre_rip
  have f101 : InstrSpec 0x10a172 [0x41, 0xC1, 0xE8, 0x04] (fun s => s.RIP = 0x10a172) (shrR32Effect 0x10a172 4 8 4)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a172 4 8 4).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10a172 0x41 0xe8 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x10a176 [0x41, 0xC1, 0xE6, 0x02] (fun s => s.RIP = 0x10a176) (shlR32Effect 0x10a176 4 14 2)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a176 4 14 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10a176 0x41 0xe6 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f103 : InstrSpec 0x10a17a [0x41, 0x31, 0xCE] (fun s => s.RIP = 0x10a17a) (xorR32R32Effect 0x10a17a 3 14 1)
      [.gpr 14, .gpr 1] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a17a 3 14 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a17a 0x41 0xce (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x10a17d [0x45, 0x31, 0xF0] (fun s => s.RIP = 0x10a17d) (xorR32R32Effect 0x10a17d 3 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a17d 3 8 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a17d 0x45 0xf0 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x10a180 [0x41, 0x81, 0xE0, 0x0F, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x10a180) (andR32Imm32Effect 0x10a180 7 8 0xf0f)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a180 7 8 0xf0f).toInstrSpec (and_r32_imm32_rex_effect_step 0x10a180 0x41 0xe0 0xf0f (by decide) (by decide) (by decide)) pre_rip
  have f106 : InstrSpec 0x10a187 [0x45, 0x89, 0xC2] (fun s => s.RIP = 0x10a187) (movR32R32Effect 0x10a187 3 10 8)
      [.gpr 8] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x10a187 3 10 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a187 0x45 0xc2 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x10a18a [0x41, 0xC1, 0xE2, 0x04] (fun s => s.RIP = 0x10a18a) (shlR32Effect 0x10a18a 4 10 4)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a18a 4 10 4).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10a18a 0x41 0xe2 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x10a18e [0x41, 0x31, 0xF2] (fun s => s.RIP = 0x10a18e) (xorR32R32Effect 0x10a18e 3 10 6)
      [.gpr 10, .gpr 6] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a18e 3 10 6).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a18e 0x41 0xf2 (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x10a191 [0x45, 0x31, 0xF0] (fun s => s.RIP = 0x10a191) (xorR32R32Effect 0x10a191 3 8 14)
      [.gpr 8, .gpr 14] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a191 3 8 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a191 0x45 0xf0 (by decide) (by decide)) pre_rip
  have f110 : InstrSpec 0x10a194 [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x10a194) (shlR32Effect 0x10a194 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a194 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10a194 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x10a198 [0x41, 0x31, 0xDB] (fun s => s.RIP = 0x10a198) (xorR32R32Effect 0x10a198 3 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a198 3 11 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a198 0x41 0xdb (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x10a19b [0x44, 0x89, 0xD8] (fun s => s.RIP = 0x10a19b) (movR32R32Effect 0x10a19b 3 0 11)
      [.gpr 11] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x10a19b 3 0 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a19b 0x44 0xd8 (by decide) (by decide)) pre_rip
  have f113 : InstrSpec 0x10a19e [0xC1, 0xE8, 0x04] (fun s => s.RIP = 0x10a19e) (shrR32Effect 0x10a19e 3 0 4)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a19e 3 0 4).toInstrSpec (shr_r32_imm8_effect_step 0x10a19e 0xe8 0x4 (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x10a1a1 [0x41, 0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x10a1a1) (shlR32Effect 0x10a1a1 4 15 2)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a1a1 4 15 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10a1a1 0x41 0xe7 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x10a1a5 [0x45, 0x31, 0xCF] (fun s => s.RIP = 0x10a1a5) (xorR32R32Effect 0x10a1a5 3 15 9)
      [.gpr 15, .gpr 9] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a1a5 3 15 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a1a5 0x45 0xcf (by decide) (by decide)) pre_rip
  have f116 : InstrSpec 0x10a1a8 [0x44, 0x31, 0xF8] (fun s => s.RIP = 0x10a1a8) (xorR32R32Effect 0x10a1a8 3 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a1a8 3 0 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a1a8 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f117 : InstrSpec 0x10a1ab [0x25, 0x0F, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x10a1ab) (andEaxImm32Effect 0x10a1ab 0xf0f)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10a1ab 0xf0f).toInstrSpec (and_eax_imm32_effect_step 0x10a1ab 0xf0f) pre_rip
  have f118 : InstrSpec 0x10a1b0 [0x89, 0xC1] (fun s => s.RIP = 0x10a1b0) (movR32R32Effect 0x10a1b0 2 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10a1b0 2 1 0).toInstrSpec (mov_r32_r32_effect_step 0x10a1b0 0xc1 (by decide)) pre_rip
  have f119 : InstrSpec 0x10a1b2 [0xC1, 0xE1, 0x04] (fun s => s.RIP = 0x10a1b2) (shlR32Effect 0x10a1b2 3 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a1b2 3 1 4).toInstrSpec (shl_r32_imm8_effect_step 0x10a1b2 0xe1 0x4 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f100 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 251), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a172) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f101 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 253), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a176) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f102 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 253), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 255), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a17a) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f103 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 253), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a17d) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f104 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 259), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a180) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f105 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 261), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a187) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f106 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 261), (9, 219), (10, 263), (11, 209), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a18a) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f107 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 261), (9, 219), (10, 265), (11, 209), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a18e) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.out (n := 267) f108 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 268) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 261), (9, 219), (10, 267), (11, 209), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a191) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 269) (RestInside.out (n := 269) f109 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 270) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 209), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a194) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 271) (RestInside.out (n := 271) f110 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 272) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 271), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a198) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 273) (RestInside.out (n := 273) f111 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 274) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a19b) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f112 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 275), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a19e) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f113 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 277), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1a1) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f114 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 280) (ρ' := [(0, 277), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 279), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1a5) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 281) (RestInside.out (n := 281) f115 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 282) (ρ' := [(0, 277), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1a8) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f116 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 283), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1ab) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 285) (RestInside.out (n := 285) f117 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 286) (ρ' := [(0, 285), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1b0) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f118 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 285), (1, 287), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1b2) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f119 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 285), (1, 289), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 269), (9, 219), (10, 267), (11, 273), (12, 193), (13, 233), (14, 257), (15, 281), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a1b5) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a008_6 code

theorem rest_l10a008_4 [Bindings] (code : CodeMap) :
    Rest (n := 211) code lifted (codeRange 0x10a008 bytes_l10a008) [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 205), (11, 209), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      59 0x10a12b bytes_l10a008_4 b_l10a008_4 := by
  have f80 : InstrSpec 0x10a12b [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x10a12b) (xorR32R32Effect 0x10a12b 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a12b 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a12b 0x45 0xda (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x10a12e [0x44, 0x89, 0xD5] (fun s => s.RIP = 0x10a12e) (movR32R32Effect 0x10a12e 3 5 10)
      [.gpr 10] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x10a12e 3 5 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a12e 0x44 0xd5 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x10a131 [0xC1, 0xED, 0x04] (fun s => s.RIP = 0x10a131) (shrR32Effect 0x10a131 3 5 4)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a131 3 5 4).toInstrSpec (shr_r32_imm8_effect_step 0x10a131 0xed 0x4 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x10a134 [0x45, 0x01, 0xC9] (fun s => s.RIP = 0x10a134) (addR32R32Effect 0x10a134 3 9 9)
      [.gpr 9, .gpr 9] [] [.reg 9, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10a134 3 9 9).toInstrSpec (add_r32_r32_rex_effect_step 0x10a134 0x45 0xc9 (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x10a137 [0x45, 0x31, 0xF9] (fun s => s.RIP = 0x10a137) (xorR32R32Effect 0x10a137 3 9 15)
      [.gpr 9, .gpr 15] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a137 3 9 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a137 0x45 0xf9 (by decide) (by decide)) pre_rip
  have f85 : InstrSpec 0x10a13a [0x45, 0x89, 0xCF] (fun s => s.RIP = 0x10a13a) (movR32R32Effect 0x10a13a 3 15 9)
      [.gpr 9] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x10a13a 3 15 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a13a 0x45 0xcf (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x10a13d [0x41, 0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x10a13d) (shrR32Effect 0x10a13d 4 15 2)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a13d 4 15 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10a13d 0x41 0xef 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x10a141 [0x45, 0x01, 0xED] (fun s => s.RIP = 0x10a141) (addR32R32Effect 0x10a141 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10a141 3 13 13).toInstrSpec (add_r32_r32_rex_effect_step 0x10a141 0x45 0xed (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x10a144 [0x41, 0x31, 0xFD] (fun s => s.RIP = 0x10a144) (xorR32R32Effect 0x10a144 3 13 7)
      [.gpr 13, .gpr 7] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a144 3 13 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a144 0x41 0xfd (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x10a147 [0x45, 0x31, 0xEF] (fun s => s.RIP = 0x10a147) (xorR32R32Effect 0x10a147 3 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a147 3 15 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a147 0x45 0xef (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x10a14a [0x41, 0x81, 0xE7, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x10a14a) (andR32Imm32Effect 0x10a14a 7 15 0x3333)
      [.gpr 15] [] [.reg 15, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a14a 7 15 0x3333).toInstrSpec (and_r32_imm32_rex_effect_step 0x10a14a 0x41 0xe7 0x3333 (by decide) (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x10a151 [0x45, 0x31, 0xFD] (fun s => s.RIP = 0x10a151) (xorR32R32Effect 0x10a151 3 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a151 3 13 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a151 0x45 0xfd (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x10a154 [0x44, 0x31, 0xED] (fun s => s.RIP = 0x10a154) (xorR32R32Effect 0x10a154 3 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a154 3 5 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a154 0x44 0xed (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x10a157 [0x81, 0xE5, 0x0F, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x10a157) (andR32Imm32Effect 0x10a157 6 5 0xf0f)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a157 6 5 0xf0f).toInstrSpec (and_r32_imm32_effect_step 0x10a157 0xe5 0xf0f (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x10a15d [0x89, 0xEF] (fun s => s.RIP = 0x10a15d) (movR32R32Effect 0x10a15d 2 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x10a15d 2 7 5).toInstrSpec (mov_r32_r32_effect_step 0x10a15d 0xef (by decide)) pre_rip
  have f95 : InstrSpec 0x10a15f [0xC1, 0xE7, 0x04] (fun s => s.RIP = 0x10a15f) (shlR32Effect 0x10a15f 3 7 4)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a15f 3 7 4).toInstrSpec (shl_r32_imm8_effect_step 0x10a15f 0xe7 0x4 (by decide) (by decide)) pre_rip
  have f96 : InstrSpec 0x10a162 [0x44, 0x31, 0xD7] (fun s => s.RIP = 0x10a162) (xorR32R32Effect 0x10a162 3 7 10)
      [.gpr 7, .gpr 10] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a162 3 7 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a162 0x44 0xd7 (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x10a165 [0x44, 0x31, 0xED] (fun s => s.RIP = 0x10a165) (xorR32R32Effect 0x10a165 3 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a165 3 5 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a165 0x44 0xed (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x10a168 [0xC1, 0xE6, 0x02] (fun s => s.RIP = 0x10a168) (shlR32Effect 0x10a168 3 6 2)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a168 3 6 2).toInstrSpec (shl_r32_imm8_effect_step 0x10a168 0xe6 0x2 (by decide) (by decide)) pre_rip
  have f99 : InstrSpec 0x10a16b [0x33, 0x74, 0x24, 0x0C] (LoadPre 0x10a16b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10a16b + BitVec.ofNat 64 4)) 4) (xorR32M32LowEffect 0x10a16b 6 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (xorR32M32LowEffect_footprint 0x10a16b 6 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (xor_r32_m32_low_effect_step 0x10a16b 6 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 211) (RestInside.out (n := 211) f80 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 212) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 211), (11, 209), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a12e) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f81 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 214) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 213), (6, 110), (7, 151), (8, 191), (9, 141), (10, 211), (11, 209), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a131) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f82 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 215), (6, 110), (7, 151), (8, 191), (9, 141), (10, 211), (11, 209), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a134) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f83 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 215), (6, 110), (7, 151), (8, 191), (9, 217), (10, 211), (11, 209), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a137) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f84 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 215), (6, 110), (7, 151), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a13a) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f85 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 215), (6, 110), (7, 151), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 171), (14, 177), (15, 221), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a13d) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f86 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 215), (6, 110), (7, 151), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 171), (14, 177), (15, 223), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a141) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f87 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 215), (6, 110), (7, 151), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 225), (14, 177), (15, 223), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a144) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f88 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 215), (6, 110), (7, 151), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 227), (14, 177), (15, 223), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a147) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.out (n := 229) f89 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 230) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 215), (6, 110), (7, 151), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 227), (14, 177), (15, 229), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a14a) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 231) (RestInside.out (n := 231) f90 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 232) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 215), (6, 110), (7, 151), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 227), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a151) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 233) (RestInside.out (n := 233) f91 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 234) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 215), (6, 110), (7, 151), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a154) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 235) (RestInside.out (n := 235) f92 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 236) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 235), (6, 110), (7, 151), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a157) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 237) (RestInside.out (n := 237) f93 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 238) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 237), (6, 110), (7, 151), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a15d) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f94 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 237), (6, 110), (7, 239), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a15f) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.out (n := 241) f95 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 242) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 237), (6, 110), (7, 241), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a162) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 243) (RestInside.out (n := 243) f96 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 244) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 237), (6, 110), (7, 243), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a165) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 245) (RestInside.out (n := 245) f97 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 246) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 110), (7, 243), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a168) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f98 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 247), (7, 243), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a16b) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f99 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 245), (6, 249), (7, 243), (8, 191), (9, 219), (10, 211), (11, 209), (12, 193), (13, 233), (14, 177), (15, 231), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a16f) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a008_5 code

theorem rest_l10a008_3 [Bindings] (code : CodeMap) :
    Rest (n := 171) code lifted (codeRange 0x10a008 bytes_l10a008) [(0, 159), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (13, 169), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      79 0x10a0df bytes_l10a008_3 b_l10a008_3 := by
  have f60 : InstrSpec 0x10a0df [0x41, 0x81, 0xE5, 0x55, 0x55, 0x00, 0x00] (fun s => s.RIP = 0x10a0df) (andR32Imm32Effect 0x10a0df 7 13 0x5555)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a0df 7 13 0x5555).toInstrSpec (and_r32_imm32_rex_effect_step 0x10a0df 0x41 0xe5 0x5555 (by decide) (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x10a0e6 [0x44, 0x31, 0xE8] (fun s => s.RIP = 0x10a0e6) (xorR32R32Effect 0x10a0e6 3 0 13)
      [.gpr 0, .gpr 13] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a0e6 3 0 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a0e6 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x10a0e9 [0x41, 0x31, 0xC6] (fun s => s.RIP = 0x10a0e9) (xorR32R32Effect 0x10a0e9 3 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a0e9 3 14 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a0e9 0x41 0xc6 (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x10a0ec [0x41, 0x81, 0xE6, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x10a0ec) (andR32Imm32Effect 0x10a0ec 7 14 0x3333)
      [.gpr 14] [] [.reg 14, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a0ec 7 14 0x3333).toInstrSpec (and_r32_imm32_rex_effect_step 0x10a0ec 0x41 0xe6 0x3333 (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x10a0f3 [0x44, 0x31, 0xF0] (fun s => s.RIP = 0x10a0f3) (xorR32R32Effect 0x10a0f3 3 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a0f3 3 0 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a0f3 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x10a0f6 [0x41, 0x31, 0xC0] (fun s => s.RIP = 0x10a0f6) (xorR32R32Effect 0x10a0f6 3 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a0f6 3 8 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a0f6 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x10a0f9 [0x41, 0x81, 0xE0, 0x0F, 0x0F, 0x00, 0x00] (fun s => s.RIP = 0x10a0f9) (andR32Imm32Effect 0x10a0f9 7 8 0xf0f)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a0f9 7 8 0xf0f).toInstrSpec (and_r32_imm32_rex_effect_step 0x10a0f9 0x41 0xe0 0xf0f (by decide) (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x10a100 [0x44, 0x89, 0xC2] (fun s => s.RIP = 0x10a100) (movR32R32Effect 0x10a100 3 2 8)
      [.gpr 8] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10a100 3 2 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a100 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x10a103 [0xC1, 0xE2, 0x04] (fun s => s.RIP = 0x10a103) (shlR32Effect 0x10a103 3 2 4)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a103 3 2 4).toInstrSpec (shl_r32_imm8_effect_step 0x10a103 0xe2 0x4 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x10a106 [0x44, 0x31, 0xE2] (fun s => s.RIP = 0x10a106) (xorR32R32Effect 0x10a106 3 2 12)
      [.gpr 2, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a106 3 2 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a106 0x44 0xe2 (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x10a109 [0x41, 0x31, 0xC0] (fun s => s.RIP = 0x10a109) (xorR32R32Effect 0x10a109 3 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a109 3 8 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a109 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x10a10c [0x45, 0x89, 0xC4] (fun s => s.RIP = 0x10a10c) (movR32R32Effect 0x10a10c 3 12 8)
      [.gpr 8] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x10a10c 3 12 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a10c 0x45 0xc4 (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x10a10f [0x01, 0xDB] (fun s => s.RIP = 0x10a10f) (addR32R32Effect 0x10a10f 2 3 3)
      [.gpr 3, .gpr 3] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10a10f 2 3 3).toInstrSpec (add_r32_r32_effect_step 0x10a10f 0xdb (by decide)) pre_rip
  have f73 : InstrSpec 0x10a111 [0x44, 0x31, 0xDB] (fun s => s.RIP = 0x10a111) (xorR32R32Effect 0x10a111 3 3 11)
      [.gpr 3, .gpr 11] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a111 3 3 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a111 0x44 0xdb (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x10a114 [0x41, 0x89, 0xDB] (fun s => s.RIP = 0x10a114) (movR32R32Effect 0x10a114 3 11 3)
      [.gpr 3] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x10a114 3 11 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a114 0x41 0xdb (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x10a117 [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x10a117) (shrR32Effect 0x10a117 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a117 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10a117 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x10a11b [0x45, 0x01, 0xD2] (fun s => s.RIP = 0x10a11b) (addR32R32Effect 0x10a11b 3 10 10)
      [.gpr 10, .gpr 10] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10a11b 3 10 10).toInstrSpec (add_r32_r32_rex_effect_step 0x10a11b 0x45 0xd2 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x10a11e [0x41, 0x31, 0xEA] (fun s => s.RIP = 0x10a11e) (xorR32R32Effect 0x10a11e 3 10 5)
      [.gpr 10, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a11e 3 10 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a11e 0x41 0xea (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x10a121 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x10a121) (xorR32R32Effect 0x10a121 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a121 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a121 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x10a124 [0x41, 0x81, 0xE3, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x10a124) (andR32Imm32Effect 0x10a124 7 11 0x3333)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a124 7 11 0x3333).toInstrSpec (and_r32_imm32_rex_effect_step 0x10a124 0x41 0xe3 0x3333 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f60 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 159), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0e6) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f61 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 173), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0e9) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f62 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 173), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 175), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0ec) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f63 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 173), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0f3) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f64 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 179), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0f6) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f65 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 179), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 181), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0f9) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f66 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 179), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 183), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a100) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f67 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 179), (1, 143), (2, 185), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 183), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a103) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f68 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 179), (1, 143), (2, 187), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 183), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a106) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f69 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 183), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a109) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f70 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 104), (11, 59), (12, 112), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a10c) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f71 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 104), (11, 59), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a10f) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f72 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 195), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 104), (11, 59), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a111) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f73 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 104), (11, 59), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a114) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f74 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 104), (11, 199), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a117) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f75 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 104), (11, 201), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a11b) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f76 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 203), (11, 201), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a11e) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f77 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 205), (11, 201), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a121) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f78 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 205), (11, 207), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a124) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f79 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 179), (1, 143), (2, 189), (3, 197), (4, 4), (5, 88), (6, 110), (7, 151), (8, 191), (9, 141), (10, 205), (11, 209), (12, 193), (13, 171), (14, 177), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a12b) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a008_4 code

theorem rest_l10a008_2 [Bindings] (code : CodeMap) :
    Rest (n := 131) code lifted (codeRange 0x10a008 bytes_l10a008) [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 121), (8, 116), (9, 129), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]
      99 0x10a095 bytes_l10a008_2 b_l10a008_2 := by
  have f40 : InstrSpec 0x10a095 [0x0F, 0xB6, 0x7A, 0x07] (LoadPre 0x10a095 (fun s => AddrMode.addr (.base 2 (.d8 0x7)) s (0x10a095 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a095 4 7 (.base 2 (.d8 0x7)))
      [.gpr 2] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10a095 4 7 (.base 2 (.d8 0x7))).toInstrSpec (movzx_r32_m8_effect_step 0x10a095 7 (.base 2 (.d8 0x7)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f41 : InstrSpec 0x10a099 [0xC1, 0xE7, 0x08] (fun s => s.RIP = 0x10a099) (shlR32Effect 0x10a099 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a099 3 7 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a099 0xe7 0x8 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x10a09c [0x0F, 0xB6, 0x4A, 0x05] (LoadPre 0x10a09c (fun s => AddrMode.addr (.base 2 (.d8 0x5)) s (0x10a09c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a09c 4 1 (.base 2 (.d8 0x5)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a09c 4 1 (.base 2 (.d8 0x5))).toInstrSpec (movzx_r32_m8_effect_step 0x10a09c 1 (.base 2 (.d8 0x5)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x10a0a0 [0x09, 0xF9] (fun s => s.RIP = 0x10a0a0) (orR32R32Effect 0x10a0a0 2 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10a0a0 2 1 7).toInstrSpec (or_r32_r32_effect_step 0x10a0a0 0xf9 (by decide)) pre_rip
  have f44 : InstrSpec 0x10a0a2 [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x10a0a2) (xorR32R32Effect 0x10a0a2 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a0a2 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a0a2 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x10a0a5 [0x41, 0x81, 0xE1, 0x55, 0x55, 0x00, 0x00] (fun s => s.RIP = 0x10a0a5) (andR32Imm32Effect 0x10a0a5 7 9 0x5555)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a0a5 7 9 0x5555).toInstrSpec (and_r32_imm32_rex_effect_step 0x10a0a5 0x41 0xe1 0x5555 (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x10a0ac [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x10a0ac) (xorR32R32Effect 0x10a0ac 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a0ac 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a0ac 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x10a0af [0x44, 0x0F, 0xB6, 0x72, 0x0B] (LoadPre 0x10a0af (fun s => AddrMode.addr (.base 2 (.d8 0xb)) s (0x10a0af + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a0af 5 14 (.base 2 (.d8 0xb)))
      [.gpr 2] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x10a0af 5 14 (.base 2 (.d8 0xb))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10a0af 0x44 (by decide) 6 (.base 2 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f48 : InstrSpec 0x10a0b4 [0x41, 0xC1, 0xE6, 0x08] (fun s => s.RIP = 0x10a0b4) (shlR32Effect 0x10a0b4 4 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a0b4 4 14 8).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10a0b4 0x41 0xe6 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x10a0b8 [0x0F, 0xB6, 0x7A, 0x09] (LoadPre 0x10a0b8 (fun s => AddrMode.addr (.base 2 (.d8 0x9)) s (0x10a0b8 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a0b8 4 7 (.base 2 (.d8 0x9)))
      [.gpr 2] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10a0b8 4 7 (.base 2 (.d8 0x9))).toInstrSpec (movzx_r32_m8_effect_step 0x10a0b8 7 (.base 2 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f50 : InstrSpec 0x10a0bc [0x44, 0x09, 0xF7] (fun s => s.RIP = 0x10a0bc) (orR32R32Effect 0x10a0bc 3 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10a0bc 3 7 14).toInstrSpec (or_r32_r32_rex_effect_step 0x10a0bc 0x44 0xf7 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x10a0bf [0x44, 0x0F, 0xB6, 0x72, 0x0F] (LoadPre 0x10a0bf (fun s => AddrMode.addr (.base 2 (.d8 0xf)) s (0x10a0bf + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a0bf 5 14 (.base 2 (.d8 0xf)))
      [.gpr 2] [] [.reg 14, .rip] :=
    (movzxR32M8Effect_footprint 0x10a0bf 5 14 (.base 2 (.d8 0xf))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10a0bf 0x44 (by decide) 6 (.base 2 (.d8 0xf)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f52 : InstrSpec 0x10a0c4 [0x41, 0xC1, 0xE6, 0x08] (fun s => s.RIP = 0x10a0c4) (shlR32Effect 0x10a0c4 4 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a0c4 4 14 8).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10a0c4 0x41 0xe6 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10a0c8 [0x0F, 0xB6, 0x42, 0x0D] (LoadPre 0x10a0c8 (fun s => AddrMode.addr (.base 2 (.d8 0xd)) s (0x10a0c8 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a0c8 4 0 (.base 2 (.d8 0xd)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a0c8 4 0 (.base 2 (.d8 0xd))).toInstrSpec (movzx_r32_m8_effect_step 0x10a0c8 0 (.base 2 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x10a0cc [0x44, 0x09, 0xF0] (fun s => s.RIP = 0x10a0cc) (orR32R32Effect 0x10a0cc 3 0 14)
      [.gpr 0, .gpr 14] [] [.reg 0, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10a0cc 3 0 14).toInstrSpec (or_r32_r32_rex_effect_step 0x10a0cc 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x10a0cf [0x41, 0x89, 0xCE] (fun s => s.RIP = 0x10a0cf) (movR32R32Effect 0x10a0cf 3 14 1)
      [.gpr 1] [] [.reg 14, .rip] :=
    (movR32R32Effect_footprint 0x10a0cf 3 14 1).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a0cf 0x41 0xce (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x10a0d2 [0x41, 0xC1, 0xEE, 0x02] (fun s => s.RIP = 0x10a0d2) (shrR32Effect 0x10a0d2 4 14 2)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a0d2 4 14 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10a0d2 0x41 0xee 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x10a0d6 [0x41, 0x89, 0xFD] (fun s => s.RIP = 0x10a0d6) (movR32R32Effect 0x10a0d6 3 13 7)
      [.gpr 7] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x10a0d6 3 13 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a0d6 0x41 0xfd (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x10a0d9 [0x41, 0xD1, 0xED] (fun s => s.RIP = 0x10a0d9) (shrR32Effect 0x10a0d9 3 13 1)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a0d9 3 13 1).toInstrSpec (shr_r32_one_rex_effect_step 0x10a0d9 0x41 0xed (by decide) (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10a0dc [0x41, 0x31, 0xC5] (fun s => s.RIP = 0x10a0dc) (xorR32R32Effect 0x10a0dc 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a0dc 3 13 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a0dc 0x41 0xc5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f40 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 131), (8, 116), (9, 129), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a099) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f41 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 133), (8, 116), (9, 129), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a09c) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 55), (1, 135), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 133), (8, 116), (9, 129), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0a0) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f43 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 55), (1, 137), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 133), (8, 116), (9, 129), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0a2) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f44 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 55), (1, 137), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 133), (8, 116), (9, 139), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0a5) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f45 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 55), (1, 137), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 133), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0ac) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 55), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 133), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0af) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f47 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 55), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 133), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (14, 145), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0b4) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f48 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 55), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 133), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (14, 147), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0b8) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f49 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 55), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 149), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (14, 147), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0bc) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f50 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 55), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (14, 147), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0bf) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f51 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 55), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (14, 153), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0c4) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f52 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 55), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (14, 155), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0c8) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 157), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (14, 155), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0cc) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f54 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 159), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (14, 155), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0cf) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f55 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 159), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (14, 161), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0d2) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f56 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 159), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0d6) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f57 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 159), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (13, 165), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0d9) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f58 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 159), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (13, 167), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0dc) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f59 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 159), (1, 143), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 151), (8, 116), (9, 141), (10, 104), (11, 59), (12, 112), (13, 169), (14, 163), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a0df) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a008_3 code

theorem rest_l10a008_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x10a008 bytes_l10a008) [(0, 55), (1, 84), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (10, 90), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      119 0x10a049 bytes_l10a008_1 b_l10a008_1 := by
  have f20 : InstrSpec 0x10a049 [0x41, 0xD1, 0xEA] (fun s => s.RIP = 0x10a049) (shrR32Effect 0x10a049 3 10 1)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a049 3 10 1).toInstrSpec (shr_r32_one_rex_effect_step 0x10a049 0x41 0xea (by decide) (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10a04c [0x0F, 0xB6, 0x4A, 0x0E] (LoadPre 0x10a04c (fun s => AddrMode.addr (.base 2 (.d8 0xe)) s (0x10a04c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a04c 4 1 (.base 2 (.d8 0xe)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a04c 4 1 (.base 2 (.d8 0xe))).toInstrSpec (movzx_r32_m8_effect_step 0x10a04c 1 (.base 2 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x10a050 [0xC1, 0xE1, 0x08] (fun s => s.RIP = 0x10a050) (shlR32Effect 0x10a050 3 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a050 3 1 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a050 0xe1 0x8 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x10a053 [0x44, 0x0F, 0xB6, 0x62, 0x0C] (LoadPre 0x10a053 (fun s => AddrMode.addr (.base 2 (.d8 0xc)) s (0x10a053 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a053 5 12 (.base 2 (.d8 0xc)))
      [.gpr 2] [] [.reg 12, .rip] :=
    (movzxR32M8Effect_footprint 0x10a053 5 12 (.base 2 (.d8 0xc))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10a053 0x44 (by decide) 4 (.base 2 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x10a058 [0x41, 0x09, 0xCC] (fun s => s.RIP = 0x10a058) (orR32R32Effect 0x10a058 3 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10a058 3 12 1).toInstrSpec (or_r32_r32_rex_effect_step 0x10a058 0x41 0xcc (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x10a05b [0x45, 0x31, 0xE2] (fun s => s.RIP = 0x10a05b) (xorR32R32Effect 0x10a05b 3 10 12)
      [.gpr 10, .gpr 12] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a05b 3 10 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a05b 0x45 0xe2 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10a05e [0x41, 0x81, 0xE2, 0x55, 0x55, 0x00, 0x00] (fun s => s.RIP = 0x10a05e) (andR32Imm32Effect 0x10a05e 7 10 0x5555)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a05e 7 10 0x5555).toInstrSpec (and_r32_imm32_rex_effect_step 0x10a05e 0x41 0xe2 0x5555 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10a065 [0x45, 0x31, 0xD4] (fun s => s.RIP = 0x10a065) (xorR32R32Effect 0x10a065 3 12 10)
      [.gpr 12, .gpr 10] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a065 3 12 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a065 0x45 0xd4 (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x10a068 [0x44, 0x31, 0xE6] (fun s => s.RIP = 0x10a068) (xorR32R32Effect 0x10a068 3 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a068 3 6 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a068 0x44 0xe6 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x10a06b [0x81, 0xE6, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x10a06b) (andR32Imm32Effect 0x10a06b 6 6 0x3333)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a06b 6 6 0x3333).toInstrSpec (and_r32_imm32_effect_step 0x10a06b 0xe6 0x3333 (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x10a071 [0x41, 0x31, 0xF4] (fun s => s.RIP = 0x10a071) (xorR32R32Effect 0x10a071 3 12 6)
      [.gpr 12, .gpr 6] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a071 3 12 6).toInstrSpec (xor_r32_r32_rex_effect_step 0x10a071 0x41 0xf4 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x10a074 [0x45, 0x89, 0xE0] (fun s => s.RIP = 0x10a074) (movR32R32Effect 0x10a074 3 8 12)
      [.gpr 12] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x10a074 3 8 12).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a074 0x45 0xe0 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10a077 [0x41, 0xC1, 0xE8, 0x04] (fun s => s.RIP = 0x10a077) (shrR32Effect 0x10a077 4 8 4)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a077 4 8 4).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10a077 0x41 0xe8 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x10a07b [0x48, 0x89, 0x7C, 0x24, 0x10] (StorePre 0x10a07b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a07b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a07b 7 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x10a07b 7 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10a07b 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f34 : InstrSpec 0x10a080 [0x0F, 0xB6, 0x7A, 0x03] (LoadPre 0x10a080 (fun s => AddrMode.addr (.base 2 (.d8 0x3)) s (0x10a080 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a080 4 7 (.base 2 (.d8 0x3)))
      [.gpr 2] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x10a080 4 7 (.base 2 (.d8 0x3))).toInstrSpec (movzx_r32_m8_effect_step 0x10a080 7 (.base 2 (.d8 0x3)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x10a084 [0xC1, 0xE7, 0x08] (fun s => s.RIP = 0x10a084) (shlR32Effect 0x10a084 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a084 3 7 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a084 0xe7 0x8 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x10a087 [0x44, 0x0F, 0xB6, 0x7A, 0x01] (LoadPre 0x10a087 (fun s => AddrMode.addr (.base 2 (.d8 0x1)) s (0x10a087 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a087 5 15 (.base 2 (.d8 0x1)))
      [.gpr 2] [] [.reg 15, .rip] :=
    (movzxR32M8Effect_footprint 0x10a087 5 15 (.base 2 (.d8 0x1))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10a087 0x44 (by decide) 7 (.base 2 (.d8 0x1)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f37 : InstrSpec 0x10a08c [0x41, 0x09, 0xFF] (fun s => s.RIP = 0x10a08c) (orR32R32Effect 0x10a08c 3 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10a08c 3 15 7).toInstrSpec (or_r32_r32_rex_effect_step 0x10a08c 0x41 0xff (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x10a08f [0x45, 0x89, 0xF9] (fun s => s.RIP = 0x10a08f) (movR32R32Effect 0x10a08f 3 9 15)
      [.gpr 15] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x10a08f 3 9 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a08f 0x45 0xf9 (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x10a092 [0x41, 0xD1, 0xE9] (fun s => s.RIP = 0x10a092) (shrR32Effect 0x10a092 3 9 1)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a092 3 9 1).toInstrSpec (shr_r32_one_rex_effect_step 0x10a092 0x41 0xe9 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f20 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 55), (1, 84), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (10, 92), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a04c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f21 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 55), (1, 94), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (10, 92), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a050) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f22 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (10, 92), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a053) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f23 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (10, 92), (11, 59), (12, 98), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a058) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f24 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (10, 92), (11, 59), (12, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a05b) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f25 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (10, 102), (11, 59), (12, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a05e) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f26 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (10, 104), (11, 59), (12, 100), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a065) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f27 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (10, 104), (11, 59), (12, 106), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a068) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f28 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 108), (7, 7), (10, 104), (11, 59), (12, 106), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a06b) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 7), (10, 104), (11, 59), (12, 106), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a071) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f30 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 7), (10, 104), (11, 59), (12, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a074) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f31 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 7), (8, 114), (10, 104), (11, 59), (12, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a077) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f32 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 7), (8, 116), (10, 104), (11, 59), (12, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a07b) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.exec (n := 118) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 7), (8, 116), (10, 104), (11, 59), (12, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a080) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f34 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 119), (8, 116), (10, 104), (11, 59), (12, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a084) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 121), (8, 116), (10, 104), (11, 59), (12, 112), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a087) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f36 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 121), (8, 116), (10, 104), (11, 59), (12, 112), (15, 123), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a08c) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f37 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 121), (8, 116), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a08f) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f38 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 121), (8, 116), (9, 127), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a092) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f39 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 55), (1, 96), (2, 2), (3, 75), (4, 4), (5, 88), (6, 110), (7, 121), (8, 116), (9, 129), (10, 104), (11, 59), (12, 112), (15, 125), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a095) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a008_2 code

theorem rest_l10a008 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a008 bytes_l10a008) (entryMap (live .l10a008))
      139 0x10a008 bytes_l10a008 b_l10a008 := by
  have f0 : InstrSpec 0x10a008 [0x0F, 0xB6, 0x42, 0x02] (LoadPre 0x10a008 (fun s => AddrMode.addr (.base 2 (.d8 0x2)) s (0x10a008 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a008 4 0 (.base 2 (.d8 0x2)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x10a008 4 0 (.base 2 (.d8 0x2))).toInstrSpec (movzx_r32_m8_effect_step 0x10a008 0 (.base 2 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10a00c [0xC1, 0xE0, 0x08] (fun s => s.RIP = 0x10a00c) (shlR32Effect 0x10a00c 3 0 8)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a00c 3 0 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a00c 0xe0 0x8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10a00f [0x44, 0x0F, 0xB6, 0x1A] (LoadPre 0x10a00f (fun s => AddrMode.addr (.base 2 .none) s (0x10a00f + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a00f 4 11 (.base 2 .none))
      [.gpr 2] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x10a00f 4 11 (.base 2 .none)).toInstrSpec (movzx_r32_m8_rex_effect_step 0x10a00f 0x44 (by decide) 3 (.base 2 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10a013 [0x41, 0x09, 0xC3] (fun s => s.RIP = 0x10a013) (orR32R32Effect 0x10a013 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10a013 3 11 0).toInstrSpec (or_r32_r32_rex_effect_step 0x10a013 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10a016 [0x44, 0x89, 0xDB] (fun s => s.RIP = 0x10a016) (movR32R32Effect 0x10a016 3 3 11)
      [.gpr 11] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x10a016 3 3 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a016 0x44 0xdb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10a019 [0xD1, 0xEB] (fun s => s.RIP = 0x10a019) (shrR32Effect 0x10a019 2 3 1)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a019 2 3 1).toInstrSpec (shr_r32_one_effect_step 0x10a019 0xeb (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10a01b [0x0F, 0xB6, 0x4A, 0x06] (LoadPre 0x10a01b (fun s => AddrMode.addr (.base 2 (.d8 0x6)) s (0x10a01b + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a01b 4 1 (.base 2 (.d8 0x6)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a01b 4 1 (.base 2 (.d8 0x6))).toInstrSpec (movzx_r32_m8_effect_step 0x10a01b 1 (.base 2 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x10a01f [0xC1, 0xE1, 0x08] (fun s => s.RIP = 0x10a01f) (shlR32Effect 0x10a01f 3 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a01f 3 1 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a01f 0xe1 0x8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10a022 [0x0F, 0xB6, 0x72, 0x04] (LoadPre 0x10a022 (fun s => AddrMode.addr (.base 2 (.d8 0x4)) s (0x10a022 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a022 4 6 (.base 2 (.d8 0x4)))
      [.gpr 2] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x10a022 4 6 (.base 2 (.d8 0x4))).toInstrSpec (movzx_r32_m8_effect_step 0x10a022 6 (.base 2 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10a026 [0x09, 0xCE] (fun s => s.RIP = 0x10a026) (orR32R32Effect 0x10a026 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10a026 2 6 1).toInstrSpec (or_r32_r32_effect_step 0x10a026 0xce (by decide)) pre_rip
  have f10 : InstrSpec 0x10a028 [0x31, 0xF3] (fun s => s.RIP = 0x10a028) (xorR32R32Effect 0x10a028 2 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a028 2 3 6).toInstrSpec (xor_r32_r32_effect_step 0x10a028 0xf3 (by decide)) pre_rip
  have f11 : InstrSpec 0x10a02a [0x81, 0xE3, 0x55, 0x55, 0x00, 0x00] (fun s => s.RIP = 0x10a02a) (andR32Imm32Effect 0x10a02a 6 3 0x5555)
      [.gpr 3] [] [.reg 3, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10a02a 6 3 0x5555).toInstrSpec (and_r32_imm32_effect_step 0x10a02a 0xe3 0x5555 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10a030 [0x31, 0xDE] (fun s => s.RIP = 0x10a030) (xorR32R32Effect 0x10a030 2 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a030 2 6 3).toInstrSpec (xor_r32_r32_effect_step 0x10a030 0xde (by decide)) pre_rip
  have f13 : InstrSpec 0x10a032 [0x89, 0x74, 0x24, 0x0C] (StorePre 0x10a032 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10a032 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10a032 6 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10a032 6 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x10a032 6 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10a036 [0xC1, 0xEE, 0x02] (fun s => s.RIP = 0x10a036) (shrR32Effect 0x10a036 3 6 2)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x10a036 3 6 2).toInstrSpec (shr_r32_imm8_effect_step 0x10a036 0xee 0x2 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x10a039 [0x0F, 0xB6, 0x4A, 0x0A] (LoadPre 0x10a039 (fun s => AddrMode.addr (.base 2 (.d8 0xa)) s (0x10a039 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a039 4 1 (.base 2 (.d8 0xa)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x10a039 4 1 (.base 2 (.d8 0xa))).toInstrSpec (movzx_r32_m8_effect_step 0x10a039 1 (.base 2 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10a03d [0xC1, 0xE1, 0x08] (fun s => s.RIP = 0x10a03d) (shlR32Effect 0x10a03d 3 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10a03d 3 1 8).toInstrSpec (shl_r32_imm8_effect_step 0x10a03d 0xe1 0x8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10a040 [0x0F, 0xB6, 0x6A, 0x08] (LoadPre 0x10a040 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x10a040 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a040 4 5 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 5, .rip] :=
    (movzxR32M8Effect_footprint 0x10a040 4 5 (.base 2 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x10a040 5 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10a044 [0x09, 0xCD] (fun s => s.RIP = 0x10a044) (orR32R32Effect 0x10a044 2 5 1)
      [.gpr 5, .gpr 1] [] [.reg 5, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10a044 2 5 1).toInstrSpec (or_r32_r32_effect_step 0x10a044 0xcd (by decide)) pre_rip
  have f19 : InstrSpec 0x10a046 [0x41, 0x89, 0xEA] (fun s => s.RIP = 0x10a046) (movR32R32Effect 0x10a046 3 10 5)
      [.gpr 5] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x10a046 3 10 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x10a046 0x41 0xea (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a00c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (4, 4), (7, 7), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a00f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (2, 2), (4, 4), (7, 7), (11, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a013) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (2, 2), (4, 4), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a016) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (2, 2), (3, 61), (4, 4), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a019) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 55), (2, 2), (3, 63), (4, 4), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a01b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 55), (1, 65), (2, 2), (3, 63), (4, 4), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a01f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 63), (4, 4), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a022) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 63), (4, 4), (6, 69), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a026) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 63), (4, 4), (6, 71), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a028) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 73), (4, 4), (6, 71), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a02a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 75), (4, 4), (6, 71), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a030) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 75), (4, 4), (6, 77), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a032) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 75), (4, 4), (6, 77), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a036) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 55), (1, 67), (2, 2), (3, 75), (4, 4), (6, 80), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a039) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 55), (1, 82), (2, 2), (3, 75), (4, 4), (6, 80), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a03d) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 55), (1, 84), (2, 2), (3, 75), (4, 4), (6, 80), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a040) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 55), (1, 84), (2, 2), (3, 75), (4, 4), (5, 86), (6, 80), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a044) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 55), (1, 84), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a046) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 55), (1, 84), (2, 2), (3, 75), (4, 4), (5, 88), (6, 80), (7, 7), (10, 90), (11, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a049) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l10a008_1 code

theorem block_l10a008 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a008 :=
  Rest.liftedBlock (rest_l10a008 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a008 x hx)

theorem rest_l10a1f1 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a1f1 bytes_l10a1f1) (entryMap (live .l10a1f1))
      5 0x10a1f1 bytes_l10a1f1 b_l10a1f1 := by
  have f0 : InstrSpec 0x10a1f1 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x10a1f1) (movR64R64Effect 0x10a1f1 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x10a1f1 2 6).toInstrSpec (mov_r64_r64_effect_step 0x10a1f1 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10a1f4 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a1f4) (movR32Imm32Effect 0x10a1f4 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10a1f4 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x10a1f4 0xbe (by decide) 0x8) pre_rip
  have f2 : InstrSpec 0x10a1f9 [0x31, 0xFF] (fun s => s.RIP = 0x10a1f9) (xorR32R32Effect 0x10a1f9 2 7 7)
      [.gpr 7, .gpr 7] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10a1f9 2 7 7).toInstrSpec (xor_r32_r32_effect_step 0x10a1f9 0xff (by decide)) pre_rip
  have f3 : InstrSpec 0x10a1fb [0x48, 0xC7, 0xC1, 0x18, 0x11, 0x20, 0x00] (fun s => s.RIP = 0x10a1fb) (movR64Imm32Effect 0x10a1fb 1 0x201118)
      [] [] [.reg 1, .rip] :=
    (movR64Imm32Effect_footprint 0x10a1fb 1 0x201118).toInstrSpec (mov_r64_imm32_effect_step 0x10a1fb 0x48 0xc1 (by decide) (by decide) (by decide) 0x201118) pre_rip
  have f4 : InstrSpec 0x10a202 [0xE8, 0x69, 0x9A, 0xFF, 0xFF] (PushPre 0x10a202 5) (callEffect (fun _ => 0x103c70) 0x10a207)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10a202 0x103c70 0x10a207).toInstrSpec (call_rel32_effect_step 0x10a202 0xffff9a69 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 53), (4, 4), (5, 5), (6, 6), (7, 7)]) (p' := 0x10a1f4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 53), (4, 4), (5, 5), (6, 55), (7, 7)]) (p' := 0x10a1f9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 53), (4, 4), (5, 5), (6, 55), (7, 57)]) (p' := 0x10a1fb) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(1, 59), (2, 53), (4, 4), (5, 5), (6, 55), (7, 57)]) (p' := 0x10a202) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(1, 59), (2, 53), (4, 61), (5, 5), (6, 55), (7, 57)]) (p' := 0x103c70) f4 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 63) (by decide) (by decide) rfl rfl

theorem block_l10a1f1 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a1f1 :=
  Rest.liftedBlock (rest_l10a1f1 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a1f1 x hx)

theorem rest_l10a207 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10a207 bytes_l10a207) (entryMap (live .l10a207))
      1 0x10a207 bytes_l10a207 b_l10a207 := by
  have f0 : InstrSpec 0x10a207 [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10a207) (fun _ => nopEffect 0x10a207 9)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10a207 9).toInstrSpec (nop_m_effect_step 0x10a207 [0x66] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10a210) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l10a207 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10a207 :=
  Rest.liftedBlock (rest_l10a207 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10a207 x hx)

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

theorem_by block_l109ff0_eval :
    program.runBlock (dialect code) ⟨.l109ff0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a008_eval :
    program.runBlock (dialect code) ⟨.l10a008, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a1f1_eval :
    program.runBlock (dialect code) ⟨.l10a1f1, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10a207_eval :
    program.runBlock (dialect code) ⟨.l10a207, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
