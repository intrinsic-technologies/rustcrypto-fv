import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l104010 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104010 bytes_l104010) (entryMap (live .l104010))
      5 0x104010 bytes_l104010 b_l104010 := by
  have f0 : InstrSpec 0x104010 [0x50] (PushPre 0x104010 1) (pushR64Effect 0x104010 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x104010 1 0).toInstrSpec (push_r64_effect_step 0x104010 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x104011 [0x49, 0x89, 0xD1] (fun s => s.RIP = 0x104011) (movR64R64Effect 0x104011 9 2)
      [.gpr 2] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x104011 9 2).toInstrSpec (mov_r64_r64_effect_step 0x104011 0x49 0xd1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104014 [0x49, 0x29, 0xC9] (fun s => s.RIP = 0x104014) (subR64R64Effect 0x104014 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x104014 9 1).toInstrSpec (sub_r64_r64_effect_step 0x104014 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104017 [0x49, 0x39, 0xF1] (fun s => s.RIP = 0x104017) (cmpR64R64Effect 0x104017 9 6)
      [.gpr 9, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x104017 9 6).toInstrSpec (cmp_r64_r64_effect_step 0x104017 0x49 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104011) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104014) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104017) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10401a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 61) (jcc_rel32_effect_step 0x10401a 3 0x32d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104010 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104010 :=
  Rest.liftedBlock (rest_l104010 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104010 x hx)

theorem rest_l104020 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104020 bytes_l104020) (entryMap (live .l104020))
      2 0x104020 bytes_l104020 b_l104020 := by
  have f0 : InstrSpec 0x104020 [0x48, 0x39, 0xF2] (fun s => s.RIP = 0x104020) (cmpR64R64Effect 0x104020 2 6)
      [.gpr 2, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x104020 2 6).toInstrSpec (cmp_r64_r64_effect_step 0x104020 0x48 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104023) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x104023 3 0x333) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104020 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104020 :=
  Rest.liftedBlock (rest_l104020 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104020 x hx)

theorem rest_l104029_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x104029 bytes_l104029) [(0, 53), (1, 84), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 88), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 90), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x104085 bytes_l104029_1 b_l104029_1 := by
  exact Rest.jcc (n := 92) (jcc_rel32_effect_step 0x104085 3 0x2c2) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l104029 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104029 bytes_l104029) (entryMap (live .l104029))
      21 0x104029 bytes_l104029 b_l104029 := by
  have f0 : InstrSpec 0x104029 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x104029) (movR64R64Effect 0x104029 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x104029 0 1).toInstrSpec (mov_r64_r64_effect_step 0x104029 0x48 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10402c [0x44, 0x0F, 0xB7, 0x14, 0x57] (LoadPre 0x10402c (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x10402c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10402c 5 10 (.sib 7 (some 2) 1 .none))
      [.gpr 7, .gpr 2] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x10402c 5 10 (.sib 7 (some 2) 1 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10402c 0x44 (by decide) 2 (.sib 7 (some 2) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x104031 [0x44, 0x89, 0xC1] (fun s => s.RIP = 0x104031) (movR32R32Effect 0x104031 3 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x104031 3 1 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x104031 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104034 [0x66, 0x41, 0xD3, 0xCA] (fun s => s.RIP = 0x104034) (rorR16ClEffect 0x104034 4 10)
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rorR16ClEffect_footprint 0x104034 4 10).toInstrSpec (ror_r16_cl_rex_effect_step 0x104034 0x41 0xca (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104038 [0x41, 0x81, 0xE2, 0x11, 0x11, 0x00, 0x00] (fun s => s.RIP = 0x104038) (andR32Imm32Effect 0x104038 7 10 0x1111)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104038 7 10 0x1111).toInstrSpec (and_r32_imm32_rex_effect_step 0x104038 0x41 0xe2 0x1111 (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10403f [0x66, 0x46, 0x33, 0x14, 0x4F] (LoadPre 0x10403f (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x10403f + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x10403f 5 10 (.sib 7 (some 9) 1 .none))
      [.gpr 10, .gpr 7, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x10403f 5 10 (.sib 7 (some 9) 1 .none)).toInstrSpec (xor_r16_m16_rex_effect_step 0x10403f 0x46 (by decide) 2 (.sib 7 (some 9) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x104044 [0x43, 0x8D, 0x0C, 0x12] (fun s => s.RIP = 0x104044) (leaR32Effect 0x104044 4 1 (.sib 10 (some 10) 0 .none))
      [.gpr 10, .gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x104044 4 1 (.sib 10 (some 10) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x104044 0x43 (by decide) 1 (.sib 10 (some 10) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104048 [0x81, 0xE1, 0xEE, 0xEE, 0xFF, 0xFF] (fun s => s.RIP = 0x104048) (andR32Imm32Effect 0x104048 6 1 0xffffeeee)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104048 6 1 0xffffeeee).toInstrSpec (and_r32_imm32_effect_step 0x104048 0xe1 0xffffeeee (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10404e [0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10404e) (leaR32Effect 0x10404e 8 9 (.abs (some 10) 2 0x0))
      [.gpr 10] [] [.reg 9, .rip] :=
    (leaR32Effect_footprint 0x10404e 8 9 (.abs (some 10) 2 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x10404e 0x46 (by decide) 1 (.abs (some 10) 2 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x104056 [0x41, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x104056) (andR32Imm32Effect 0x104056 7 9 0xffffcccc)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104056 7 9 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x104056 0x41 0xe1 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10405d [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x10405d) (xorR32R32Effect 0x10405d 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10405d 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x10405d 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x104060 [0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104060) (leaR32Effect 0x104060 8 1 (.abs (some 10) 3 0x0))
      [.gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x104060 8 1 (.abs (some 10) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x104060 0x42 (by decide) 1 (.abs (some 10) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x104068 [0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x104068) (andR32Imm32Effect 0x104068 6 1 0xffff8888)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104068 6 1 0xffff8888).toInstrSpec (and_r32_imm32_effect_step 0x104068 0xe1 0xffff8888 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10406e [0x44, 0x31, 0xD1] (fun s => s.RIP = 0x10406e) (xorR32R32Effect 0x10406e 3 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10406e 3 1 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10406e 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x104071 [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x104071) (xorR32R32Effect 0x104071 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104071 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104071 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x104074 [0x66, 0x89, 0x0C, 0x57] (StorePre 0x104074 4 (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x104074 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x104074 4 1 (.sib 7 (some 2) 1 .none))
      [.gpr 1, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x104074 4 1 (.sib 7 (some 2) 1 .none)).toInstrSpec (mov_m16_r16_effect_step 0x104074 1 (.sib 7 (some 2) 1 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x104078 [0x48, 0x8D, 0x4A, 0x01] (fun s => s.RIP = 0x104078) (leaR64Effect 0x104078 1 (.base 2 (.d8 0x1)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x104078 1 (.base 2 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x104078 0x48 (by decide) 1 (.base 2 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10407c [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x10407c) (movR64R64Effect 0x10407c 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10407c 9 1).toInstrSpec (mov_r64_r64_effect_step 0x10407c 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10407f [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x10407f) (subR64R64Effect 0x10407f 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x10407f 9 0).toInstrSpec (sub_r64_r64_effect_step 0x10407f 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x104082 [0x49, 0x39, 0xF1] (fun s => s.RIP = 0x104082) (cmpR64R64Effect 0x104082 9 6)
      [.gpr 9, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x104082 9 6).toInstrSpec (cmp_r64_r64_effect_step 0x104082 0x49 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10402c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104031) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104034) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104038) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10403f) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104044) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104048) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10404e) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 53), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104056) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 53), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10405d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 73), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104060) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 53), (1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 73), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104068) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 53), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 73), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10406e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 53), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 73), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104071) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 53), (1, 81), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 73), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104074) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 53), (1, 81), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 73), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104078) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 53), (1, 84), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 73), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10407c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 53), (1, 84), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10407f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 53), (1, 84), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 88), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104082) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 53), (1, 84), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 88), (10, 63), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 90), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104085) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l104029_1 code

theorem block_l104029 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104029 :=
  Rest.liftedBlock (rest_l104029 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104029 x hx)

theorem rest_l10408b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10408b bytes_l10408b) (entryMap (live .l10408b))
      2 0x10408b bytes_l10408b b_l10408b := by
  have f0 : InstrSpec 0x10408b [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x10408b) (cmpR64R64Effect 0x10408b 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x10408b 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x10408b 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10408e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x10408e 3 0x2cb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10408b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10408b :=
  Rest.liftedBlock (rest_l10408b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10408b x hx)

theorem rest_l104094 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104094 bytes_l104094) (entryMap (live .l104094))
      20 0x104094 bytes_l104094 b_l104094 := by
  have f0 : InstrSpec 0x104094 [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x02] (LoadPre 0x104094 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x2)) s (0x104094 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104094 6 10 (.sib 7 (some 2) 1 (.d8 0x2)))
      [.gpr 7, .gpr 2] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x104094 6 10 (.sib 7 (some 2) 1 (.d8 0x2))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x104094 0x44 (by decide) 2 (.sib 7 (some 2) 1 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10409a [0x44, 0x89, 0xC1] (fun s => s.RIP = 0x10409a) (movR32R32Effect 0x10409a 3 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10409a 3 1 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x10409a 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10409d [0x66, 0x41, 0xD3, 0xCA] (fun s => s.RIP = 0x10409d) (rorR16ClEffect 0x10409d 4 10)
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rorR16ClEffect_footprint 0x10409d 4 10).toInstrSpec (ror_r16_cl_rex_effect_step 0x10409d 0x41 0xca (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1040a1 [0x41, 0x81, 0xE2, 0x11, 0x11, 0x00, 0x00] (fun s => s.RIP = 0x1040a1) (andR32Imm32Effect 0x1040a1 7 10 0x1111)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1040a1 7 10 0x1111).toInstrSpec (and_r32_imm32_rex_effect_step 0x1040a1 0x41 0xe2 0x1111 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1040a8 [0x66, 0x46, 0x33, 0x14, 0x4F] (LoadPre 0x1040a8 (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x1040a8 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x1040a8 5 10 (.sib 7 (some 9) 1 .none))
      [.gpr 10, .gpr 7, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1040a8 5 10 (.sib 7 (some 9) 1 .none)).toInstrSpec (xor_r16_m16_rex_effect_step 0x1040a8 0x46 (by decide) 2 (.sib 7 (some 9) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1040ad [0x43, 0x8D, 0x0C, 0x12] (fun s => s.RIP = 0x1040ad) (leaR32Effect 0x1040ad 4 1 (.sib 10 (some 10) 0 .none))
      [.gpr 10, .gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x1040ad 4 1 (.sib 10 (some 10) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x1040ad 0x43 (by decide) 1 (.sib 10 (some 10) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1040b1 [0x81, 0xE1, 0xEE, 0xEE, 0xFF, 0xFF] (fun s => s.RIP = 0x1040b1) (andR32Imm32Effect 0x1040b1 6 1 0xffffeeee)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1040b1 6 1 0xffffeeee).toInstrSpec (and_r32_imm32_effect_step 0x1040b1 0xe1 0xffffeeee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1040b7 [0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1040b7) (leaR32Effect 0x1040b7 8 9 (.abs (some 10) 2 0x0))
      [.gpr 10] [] [.reg 9, .rip] :=
    (leaR32Effect_footprint 0x1040b7 8 9 (.abs (some 10) 2 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x1040b7 0x46 (by decide) 1 (.abs (some 10) 2 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1040bf [0x41, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x1040bf) (andR32Imm32Effect 0x1040bf 7 9 0xffffcccc)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1040bf 7 9 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x1040bf 0x41 0xe1 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1040c6 [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x1040c6) (xorR32R32Effect 0x1040c6 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1040c6 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x1040c6 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1040c9 [0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1040c9) (leaR32Effect 0x1040c9 8 1 (.abs (some 10) 3 0x0))
      [.gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x1040c9 8 1 (.abs (some 10) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x1040c9 0x42 (by decide) 1 (.abs (some 10) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1040d1 [0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x1040d1) (andR32Imm32Effect 0x1040d1 6 1 0xffff8888)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1040d1 6 1 0xffff8888).toInstrSpec (and_r32_imm32_effect_step 0x1040d1 0xe1 0xffff8888 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1040d7 [0x44, 0x31, 0xD1] (fun s => s.RIP = 0x1040d7) (xorR32R32Effect 0x1040d7 3 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1040d7 3 1 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1040d7 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1040da [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x1040da) (xorR32R32Effect 0x1040da 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1040da 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1040da 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1040dd [0x66, 0x89, 0x4C, 0x57, 0x02] (StorePre 0x1040dd 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x2)) s (0x1040dd + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1040dd 5 1 (.sib 7 (some 2) 1 (.d8 0x2)))
      [.gpr 1, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x1040dd 5 1 (.sib 7 (some 2) 1 (.d8 0x2))).toInstrSpec (mov_m16_r16_effect_step 0x1040dd 1 (.sib 7 (some 2) 1 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1040e2 [0x48, 0x8D, 0x4A, 0x02] (fun s => s.RIP = 0x1040e2) (leaR64Effect 0x1040e2 1 (.base 2 (.d8 0x2)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1040e2 1 (.base 2 (.d8 0x2))).toInstrSpec (lea_r64_effect_step 0x1040e2 0x48 (by decide) 1 (.base 2 (.d8 0x2)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1040e6 [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x1040e6) (movR64R64Effect 0x1040e6 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1040e6 9 1).toInstrSpec (mov_r64_r64_effect_step 0x1040e6 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1040e9 [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x1040e9) (subR64R64Effect 0x1040e9 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1040e9 9 0).toInstrSpec (sub_r64_r64_effect_step 0x1040e9 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1040ec [0x49, 0x39, 0xF1] (fun s => s.RIP = 0x1040ec) (cmpR64R64Effect 0x1040ec 9 6)
      [.gpr 9, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1040ec 9 6).toInstrSpec (cmp_r64_r64_effect_step 0x1040ec 0x49 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10409a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10409d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040a1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040a8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040ad) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040b1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040b7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 67), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040bf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040c6) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040c9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040d1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040d7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040da) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040dd) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040e2) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040e6) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 84), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040e9) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040ec) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040ef) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel32_effect_step 0x1040ef 3 0x258) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104094 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104094 :=
  Rest.liftedBlock (rest_l104094 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104094 x hx)

theorem rest_l1040f5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1040f5 bytes_l1040f5) (entryMap (live .l1040f5))
      2 0x1040f5 bytes_l1040f5 b_l1040f5 := by
  have f0 : InstrSpec 0x1040f5 [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x1040f5) (cmpR64R64Effect 0x1040f5 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1040f5 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x1040f5 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1040f8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1040f8 3 0x261) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1040f5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1040f5 :=
  Rest.liftedBlock (rest_l1040f5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1040f5 x hx)

theorem rest_l1040fe [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1040fe bytes_l1040fe) (entryMap (live .l1040fe))
      20 0x1040fe bytes_l1040fe b_l1040fe := by
  have f0 : InstrSpec 0x1040fe [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x04] (LoadPre 0x1040fe (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x4)) s (0x1040fe + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1040fe 6 10 (.sib 7 (some 2) 1 (.d8 0x4)))
      [.gpr 7, .gpr 2] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x1040fe 6 10 (.sib 7 (some 2) 1 (.d8 0x4))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1040fe 0x44 (by decide) 2 (.sib 7 (some 2) 1 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104104 [0x44, 0x89, 0xC1] (fun s => s.RIP = 0x104104) (movR32R32Effect 0x104104 3 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x104104 3 1 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x104104 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104107 [0x66, 0x41, 0xD3, 0xCA] (fun s => s.RIP = 0x104107) (rorR16ClEffect 0x104107 4 10)
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rorR16ClEffect_footprint 0x104107 4 10).toInstrSpec (ror_r16_cl_rex_effect_step 0x104107 0x41 0xca (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10410b [0x41, 0x81, 0xE2, 0x11, 0x11, 0x00, 0x00] (fun s => s.RIP = 0x10410b) (andR32Imm32Effect 0x10410b 7 10 0x1111)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10410b 7 10 0x1111).toInstrSpec (and_r32_imm32_rex_effect_step 0x10410b 0x41 0xe2 0x1111 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104112 [0x66, 0x46, 0x33, 0x14, 0x4F] (LoadPre 0x104112 (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x104112 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x104112 5 10 (.sib 7 (some 9) 1 .none))
      [.gpr 10, .gpr 7, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x104112 5 10 (.sib 7 (some 9) 1 .none)).toInstrSpec (xor_r16_m16_rex_effect_step 0x104112 0x46 (by decide) 2 (.sib 7 (some 9) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x104117 [0x43, 0x8D, 0x0C, 0x12] (fun s => s.RIP = 0x104117) (leaR32Effect 0x104117 4 1 (.sib 10 (some 10) 0 .none))
      [.gpr 10, .gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x104117 4 1 (.sib 10 (some 10) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x104117 0x43 (by decide) 1 (.sib 10 (some 10) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10411b [0x81, 0xE1, 0xEE, 0xEE, 0xFF, 0xFF] (fun s => s.RIP = 0x10411b) (andR32Imm32Effect 0x10411b 6 1 0xffffeeee)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10411b 6 1 0xffffeeee).toInstrSpec (and_r32_imm32_effect_step 0x10411b 0xe1 0xffffeeee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104121 [0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104121) (leaR32Effect 0x104121 8 9 (.abs (some 10) 2 0x0))
      [.gpr 10] [] [.reg 9, .rip] :=
    (leaR32Effect_footprint 0x104121 8 9 (.abs (some 10) 2 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x104121 0x46 (by decide) 1 (.abs (some 10) 2 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x104129 [0x41, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x104129) (andR32Imm32Effect 0x104129 7 9 0xffffcccc)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104129 7 9 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x104129 0x41 0xe1 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x104130 [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x104130) (xorR32R32Effect 0x104130 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104130 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x104130 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x104133 [0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104133) (leaR32Effect 0x104133 8 1 (.abs (some 10) 3 0x0))
      [.gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x104133 8 1 (.abs (some 10) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x104133 0x42 (by decide) 1 (.abs (some 10) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10413b [0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x10413b) (andR32Imm32Effect 0x10413b 6 1 0xffff8888)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10413b 6 1 0xffff8888).toInstrSpec (and_r32_imm32_effect_step 0x10413b 0xe1 0xffff8888 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x104141 [0x44, 0x31, 0xD1] (fun s => s.RIP = 0x104141) (xorR32R32Effect 0x104141 3 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104141 3 1 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104141 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x104144 [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x104144) (xorR32R32Effect 0x104144 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104144 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104144 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x104147 [0x66, 0x89, 0x4C, 0x57, 0x04] (StorePre 0x104147 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x4)) s (0x104147 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104147 5 1 (.sib 7 (some 2) 1 (.d8 0x4)))
      [.gpr 1, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x104147 5 1 (.sib 7 (some 2) 1 (.d8 0x4))).toInstrSpec (mov_m16_r16_effect_step 0x104147 1 (.sib 7 (some 2) 1 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10414c [0x48, 0x8D, 0x4A, 0x03] (fun s => s.RIP = 0x10414c) (leaR64Effect 0x10414c 1 (.base 2 (.d8 0x3)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x10414c 1 (.base 2 (.d8 0x3))).toInstrSpec (lea_r64_effect_step 0x10414c 0x48 (by decide) 1 (.base 2 (.d8 0x3)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x104150 [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x104150) (movR64R64Effect 0x104150 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x104150 9 1).toInstrSpec (mov_r64_r64_effect_step 0x104150 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x104153 [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x104153) (subR64R64Effect 0x104153 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x104153 9 0).toInstrSpec (sub_r64_r64_effect_step 0x104153 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x104156 [0x49, 0x39, 0xF1] (fun s => s.RIP = 0x104156) (cmpR64R64Effect 0x104156 9 6)
      [.gpr 9, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x104156 9 6).toInstrSpec (cmp_r64_r64_effect_step 0x104156 0x49 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104104) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104107) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10410b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104112) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104117) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10411b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104121) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 67), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104129) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104130) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104133) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10413b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104141) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104144) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104147) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10414c) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104150) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 84), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104153) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104156) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104159) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel32_effect_step 0x104159 3 0x1ee) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1040fe [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1040fe :=
  Rest.liftedBlock (rest_l1040fe code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1040fe x hx)

theorem rest_l10415f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10415f bytes_l10415f) (entryMap (live .l10415f))
      2 0x10415f bytes_l10415f b_l10415f := by
  have f0 : InstrSpec 0x10415f [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x10415f) (cmpR64R64Effect 0x10415f 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x10415f 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x10415f 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104162) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x104162 3 0x1f7) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10415f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10415f :=
  Rest.liftedBlock (rest_l10415f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10415f x hx)

theorem rest_l104168 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104168 bytes_l104168) (entryMap (live .l104168))
      20 0x104168 bytes_l104168 b_l104168 := by
  have f0 : InstrSpec 0x104168 [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x06] (LoadPre 0x104168 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x6)) s (0x104168 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x104168 6 10 (.sib 7 (some 2) 1 (.d8 0x6)))
      [.gpr 7, .gpr 2] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x104168 6 10 (.sib 7 (some 2) 1 (.d8 0x6))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x104168 0x44 (by decide) 2 (.sib 7 (some 2) 1 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10416e [0x44, 0x89, 0xC1] (fun s => s.RIP = 0x10416e) (movR32R32Effect 0x10416e 3 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10416e 3 1 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x10416e 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104171 [0x66, 0x41, 0xD3, 0xCA] (fun s => s.RIP = 0x104171) (rorR16ClEffect 0x104171 4 10)
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rorR16ClEffect_footprint 0x104171 4 10).toInstrSpec (ror_r16_cl_rex_effect_step 0x104171 0x41 0xca (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104175 [0x41, 0x81, 0xE2, 0x11, 0x11, 0x00, 0x00] (fun s => s.RIP = 0x104175) (andR32Imm32Effect 0x104175 7 10 0x1111)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104175 7 10 0x1111).toInstrSpec (and_r32_imm32_rex_effect_step 0x104175 0x41 0xe2 0x1111 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10417c [0x66, 0x46, 0x33, 0x14, 0x4F] (LoadPre 0x10417c (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x10417c + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x10417c 5 10 (.sib 7 (some 9) 1 .none))
      [.gpr 10, .gpr 7, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x10417c 5 10 (.sib 7 (some 9) 1 .none)).toInstrSpec (xor_r16_m16_rex_effect_step 0x10417c 0x46 (by decide) 2 (.sib 7 (some 9) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x104181 [0x43, 0x8D, 0x0C, 0x12] (fun s => s.RIP = 0x104181) (leaR32Effect 0x104181 4 1 (.sib 10 (some 10) 0 .none))
      [.gpr 10, .gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x104181 4 1 (.sib 10 (some 10) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x104181 0x43 (by decide) 1 (.sib 10 (some 10) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104185 [0x81, 0xE1, 0xEE, 0xEE, 0xFF, 0xFF] (fun s => s.RIP = 0x104185) (andR32Imm32Effect 0x104185 6 1 0xffffeeee)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104185 6 1 0xffffeeee).toInstrSpec (and_r32_imm32_effect_step 0x104185 0xe1 0xffffeeee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10418b [0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10418b) (leaR32Effect 0x10418b 8 9 (.abs (some 10) 2 0x0))
      [.gpr 10] [] [.reg 9, .rip] :=
    (leaR32Effect_footprint 0x10418b 8 9 (.abs (some 10) 2 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x10418b 0x46 (by decide) 1 (.abs (some 10) 2 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x104193 [0x41, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x104193) (andR32Imm32Effect 0x104193 7 9 0xffffcccc)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104193 7 9 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x104193 0x41 0xe1 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10419a [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x10419a) (xorR32R32Effect 0x10419a 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10419a 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x10419a 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10419d [0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10419d) (leaR32Effect 0x10419d 8 1 (.abs (some 10) 3 0x0))
      [.gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x10419d 8 1 (.abs (some 10) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x10419d 0x42 (by decide) 1 (.abs (some 10) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1041a5 [0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x1041a5) (andR32Imm32Effect 0x1041a5 6 1 0xffff8888)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1041a5 6 1 0xffff8888).toInstrSpec (and_r32_imm32_effect_step 0x1041a5 0xe1 0xffff8888 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1041ab [0x44, 0x31, 0xD1] (fun s => s.RIP = 0x1041ab) (xorR32R32Effect 0x1041ab 3 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1041ab 3 1 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1041ab 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1041ae [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x1041ae) (xorR32R32Effect 0x1041ae 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1041ae 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1041ae 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1041b1 [0x66, 0x89, 0x4C, 0x57, 0x06] (StorePre 0x1041b1 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x6)) s (0x1041b1 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1041b1 5 1 (.sib 7 (some 2) 1 (.d8 0x6)))
      [.gpr 1, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x1041b1 5 1 (.sib 7 (some 2) 1 (.d8 0x6))).toInstrSpec (mov_m16_r16_effect_step 0x1041b1 1 (.sib 7 (some 2) 1 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1041b6 [0x48, 0x8D, 0x4A, 0x04] (fun s => s.RIP = 0x1041b6) (leaR64Effect 0x1041b6 1 (.base 2 (.d8 0x4)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1041b6 1 (.base 2 (.d8 0x4))).toInstrSpec (lea_r64_effect_step 0x1041b6 0x48 (by decide) 1 (.base 2 (.d8 0x4)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1041ba [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x1041ba) (movR64R64Effect 0x1041ba 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1041ba 9 1).toInstrSpec (mov_r64_r64_effect_step 0x1041ba 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1041bd [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x1041bd) (subR64R64Effect 0x1041bd 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1041bd 9 0).toInstrSpec (sub_r64_r64_effect_step 0x1041bd 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1041c0 [0x49, 0x39, 0xF1] (fun s => s.RIP = 0x1041c0) (cmpR64R64Effect 0x1041c0 9 6)
      [.gpr 9, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1041c0 9 6).toInstrSpec (cmp_r64_r64_effect_step 0x1041c0 0x49 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10416e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104171) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104175) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10417c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104181) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104185) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10418b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 67), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104193) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10419a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10419d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041a5) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041ab) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041ae) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041b1) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041b6) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041ba) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 84), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041bd) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041c0) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041c3) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel32_effect_step 0x1041c3 3 0x184) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104168 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104168 :=
  Rest.liftedBlock (rest_l104168 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104168 x hx)

theorem rest_l1041c9 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1041c9 bytes_l1041c9) (entryMap (live .l1041c9))
      2 0x1041c9 bytes_l1041c9 b_l1041c9 := by
  have f0 : InstrSpec 0x1041c9 [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x1041c9) (cmpR64R64Effect 0x1041c9 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1041c9 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x1041c9 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041cc) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1041cc 3 0x18d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1041c9 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1041c9 :=
  Rest.liftedBlock (rest_l1041c9 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1041c9 x hx)

theorem rest_l1041d2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1041d2 bytes_l1041d2) (entryMap (live .l1041d2))
      20 0x1041d2 bytes_l1041d2 b_l1041d2 := by
  have f0 : InstrSpec 0x1041d2 [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x08] (LoadPre 0x1041d2 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x8)) s (0x1041d2 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1041d2 6 10 (.sib 7 (some 2) 1 (.d8 0x8)))
      [.gpr 7, .gpr 2] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x1041d2 6 10 (.sib 7 (some 2) 1 (.d8 0x8))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1041d2 0x44 (by decide) 2 (.sib 7 (some 2) 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1041d8 [0x44, 0x89, 0xC1] (fun s => s.RIP = 0x1041d8) (movR32R32Effect 0x1041d8 3 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1041d8 3 1 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x1041d8 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1041db [0x66, 0x41, 0xD3, 0xCA] (fun s => s.RIP = 0x1041db) (rorR16ClEffect 0x1041db 4 10)
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rorR16ClEffect_footprint 0x1041db 4 10).toInstrSpec (ror_r16_cl_rex_effect_step 0x1041db 0x41 0xca (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1041df [0x41, 0x81, 0xE2, 0x11, 0x11, 0x00, 0x00] (fun s => s.RIP = 0x1041df) (andR32Imm32Effect 0x1041df 7 10 0x1111)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1041df 7 10 0x1111).toInstrSpec (and_r32_imm32_rex_effect_step 0x1041df 0x41 0xe2 0x1111 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1041e6 [0x66, 0x46, 0x33, 0x14, 0x4F] (LoadPre 0x1041e6 (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x1041e6 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x1041e6 5 10 (.sib 7 (some 9) 1 .none))
      [.gpr 10, .gpr 7, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1041e6 5 10 (.sib 7 (some 9) 1 .none)).toInstrSpec (xor_r16_m16_rex_effect_step 0x1041e6 0x46 (by decide) 2 (.sib 7 (some 9) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1041eb [0x43, 0x8D, 0x0C, 0x12] (fun s => s.RIP = 0x1041eb) (leaR32Effect 0x1041eb 4 1 (.sib 10 (some 10) 0 .none))
      [.gpr 10, .gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x1041eb 4 1 (.sib 10 (some 10) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x1041eb 0x43 (by decide) 1 (.sib 10 (some 10) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1041ef [0x81, 0xE1, 0xEE, 0xEE, 0xFF, 0xFF] (fun s => s.RIP = 0x1041ef) (andR32Imm32Effect 0x1041ef 6 1 0xffffeeee)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1041ef 6 1 0xffffeeee).toInstrSpec (and_r32_imm32_effect_step 0x1041ef 0xe1 0xffffeeee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1041f5 [0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1041f5) (leaR32Effect 0x1041f5 8 9 (.abs (some 10) 2 0x0))
      [.gpr 10] [] [.reg 9, .rip] :=
    (leaR32Effect_footprint 0x1041f5 8 9 (.abs (some 10) 2 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x1041f5 0x46 (by decide) 1 (.abs (some 10) 2 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1041fd [0x41, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x1041fd) (andR32Imm32Effect 0x1041fd 7 9 0xffffcccc)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1041fd 7 9 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x1041fd 0x41 0xe1 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x104204 [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x104204) (xorR32R32Effect 0x104204 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104204 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x104204 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x104207 [0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104207) (leaR32Effect 0x104207 8 1 (.abs (some 10) 3 0x0))
      [.gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x104207 8 1 (.abs (some 10) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x104207 0x42 (by decide) 1 (.abs (some 10) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10420f [0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x10420f) (andR32Imm32Effect 0x10420f 6 1 0xffff8888)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10420f 6 1 0xffff8888).toInstrSpec (and_r32_imm32_effect_step 0x10420f 0xe1 0xffff8888 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x104215 [0x44, 0x31, 0xD1] (fun s => s.RIP = 0x104215) (xorR32R32Effect 0x104215 3 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104215 3 1 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x104215 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x104218 [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x104218) (xorR32R32Effect 0x104218 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104218 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104218 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x10421b [0x66, 0x89, 0x4C, 0x57, 0x08] (StorePre 0x10421b 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x8)) s (0x10421b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10421b 5 1 (.sib 7 (some 2) 1 (.d8 0x8)))
      [.gpr 1, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x10421b 5 1 (.sib 7 (some 2) 1 (.d8 0x8))).toInstrSpec (mov_m16_r16_effect_step 0x10421b 1 (.sib 7 (some 2) 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x104220 [0x48, 0x8D, 0x4A, 0x05] (fun s => s.RIP = 0x104220) (leaR64Effect 0x104220 1 (.base 2 (.d8 0x5)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x104220 1 (.base 2 (.d8 0x5))).toInstrSpec (lea_r64_effect_step 0x104220 0x48 (by decide) 1 (.base 2 (.d8 0x5)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x104224 [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x104224) (movR64R64Effect 0x104224 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x104224 9 1).toInstrSpec (mov_r64_r64_effect_step 0x104224 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x104227 [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x104227) (subR64R64Effect 0x104227 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x104227 9 0).toInstrSpec (sub_r64_r64_effect_step 0x104227 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10422a [0x49, 0x39, 0xF1] (fun s => s.RIP = 0x10422a) (cmpR64R64Effect 0x10422a 9 6)
      [.gpr 9, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x10422a 9 6).toInstrSpec (cmp_r64_r64_effect_step 0x10422a 0x49 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041d8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041db) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041df) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041e6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041eb) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041ef) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041f5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 67), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1041fd) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104204) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104207) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10420f) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104215) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104218) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10421b) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104220) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104224) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 84), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104227) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10422a) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10422d) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel32_effect_step 0x10422d 3 0x11a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1041d2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1041d2 :=
  Rest.liftedBlock (rest_l1041d2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1041d2 x hx)

theorem rest_l104233 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104233 bytes_l104233) (entryMap (live .l104233))
      2 0x104233 bytes_l104233 b_l104233 := by
  have f0 : InstrSpec 0x104233 [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x104233) (cmpR64R64Effect 0x104233 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x104233 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x104233 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104236) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x104236 3 0x123) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104233 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104233 :=
  Rest.liftedBlock (rest_l104233 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104233 x hx)

theorem rest_l10423c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10423c bytes_l10423c) (entryMap (live .l10423c))
      20 0x10423c bytes_l10423c b_l10423c := by
  have f0 : InstrSpec 0x10423c [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x0A] (LoadPre 0x10423c (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xa)) s (0x10423c + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10423c 6 10 (.sib 7 (some 2) 1 (.d8 0xa)))
      [.gpr 7, .gpr 2] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x10423c 6 10 (.sib 7 (some 2) 1 (.d8 0xa))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10423c 0x44 (by decide) 2 (.sib 7 (some 2) 1 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x104242 [0x44, 0x89, 0xC1] (fun s => s.RIP = 0x104242) (movR32R32Effect 0x104242 3 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x104242 3 1 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x104242 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104245 [0x66, 0x41, 0xD3, 0xCA] (fun s => s.RIP = 0x104245) (rorR16ClEffect 0x104245 4 10)
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rorR16ClEffect_footprint 0x104245 4 10).toInstrSpec (ror_r16_cl_rex_effect_step 0x104245 0x41 0xca (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104249 [0x41, 0x81, 0xE2, 0x11, 0x11, 0x00, 0x00] (fun s => s.RIP = 0x104249) (andR32Imm32Effect 0x104249 7 10 0x1111)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104249 7 10 0x1111).toInstrSpec (and_r32_imm32_rex_effect_step 0x104249 0x41 0xe2 0x1111 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x104250 [0x66, 0x46, 0x33, 0x14, 0x4F] (LoadPre 0x104250 (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x104250 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x104250 5 10 (.sib 7 (some 9) 1 .none))
      [.gpr 10, .gpr 7, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x104250 5 10 (.sib 7 (some 9) 1 .none)).toInstrSpec (xor_r16_m16_rex_effect_step 0x104250 0x46 (by decide) 2 (.sib 7 (some 9) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x104255 [0x43, 0x8D, 0x0C, 0x12] (fun s => s.RIP = 0x104255) (leaR32Effect 0x104255 4 1 (.sib 10 (some 10) 0 .none))
      [.gpr 10, .gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x104255 4 1 (.sib 10 (some 10) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x104255 0x43 (by decide) 1 (.sib 10 (some 10) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104259 [0x81, 0xE1, 0xEE, 0xEE, 0xFF, 0xFF] (fun s => s.RIP = 0x104259) (andR32Imm32Effect 0x104259 6 1 0xffffeeee)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104259 6 1 0xffffeeee).toInstrSpec (and_r32_imm32_effect_step 0x104259 0xe1 0xffffeeee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10425f [0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10425f) (leaR32Effect 0x10425f 8 9 (.abs (some 10) 2 0x0))
      [.gpr 10] [] [.reg 9, .rip] :=
    (leaR32Effect_footprint 0x10425f 8 9 (.abs (some 10) 2 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x10425f 0x46 (by decide) 1 (.abs (some 10) 2 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x104267 [0x41, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x104267) (andR32Imm32Effect 0x104267 7 9 0xffffcccc)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104267 7 9 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x104267 0x41 0xe1 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10426e [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x10426e) (xorR32R32Effect 0x10426e 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10426e 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x10426e 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x104271 [0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104271) (leaR32Effect 0x104271 8 1 (.abs (some 10) 3 0x0))
      [.gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x104271 8 1 (.abs (some 10) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x104271 0x42 (by decide) 1 (.abs (some 10) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x104279 [0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x104279) (andR32Imm32Effect 0x104279 6 1 0xffff8888)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104279 6 1 0xffff8888).toInstrSpec (and_r32_imm32_effect_step 0x104279 0xe1 0xffff8888 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10427f [0x44, 0x31, 0xD1] (fun s => s.RIP = 0x10427f) (xorR32R32Effect 0x10427f 3 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10427f 3 1 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10427f 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x104282 [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x104282) (xorR32R32Effect 0x104282 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104282 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x104282 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x104285 [0x66, 0x89, 0x4C, 0x57, 0x0A] (StorePre 0x104285 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xa)) s (0x104285 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104285 5 1 (.sib 7 (some 2) 1 (.d8 0xa)))
      [.gpr 1, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x104285 5 1 (.sib 7 (some 2) 1 (.d8 0xa))).toInstrSpec (mov_m16_r16_effect_step 0x104285 1 (.sib 7 (some 2) 1 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10428a [0x48, 0x8D, 0x4A, 0x06] (fun s => s.RIP = 0x10428a) (leaR64Effect 0x10428a 1 (.base 2 (.d8 0x6)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x10428a 1 (.base 2 (.d8 0x6))).toInstrSpec (lea_r64_effect_step 0x10428a 0x48 (by decide) 1 (.base 2 (.d8 0x6)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x10428e [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x10428e) (movR64R64Effect 0x10428e 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x10428e 9 1).toInstrSpec (mov_r64_r64_effect_step 0x10428e 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x104291 [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x104291) (subR64R64Effect 0x104291 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x104291 9 0).toInstrSpec (sub_r64_r64_effect_step 0x104291 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x104294 [0x49, 0x39, 0xF1] (fun s => s.RIP = 0x104294) (cmpR64R64Effect 0x104294 9 6)
      [.gpr 9, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x104294 9 6).toInstrSpec (cmp_r64_r64_effect_step 0x104294 0x49 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104242) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104245) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104249) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104250) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104255) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104259) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10425f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 67), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104267) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10426e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104271) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104279) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10427f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104282) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104285) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10428a) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10428e) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 84), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104291) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104294) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104297) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel32_effect_step 0x104297 3 0xb0) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10423c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10423c :=
  Rest.liftedBlock (rest_l10423c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10423c x hx)

theorem rest_l10429d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10429d bytes_l10429d) (entryMap (live .l10429d))
      2 0x10429d bytes_l10429d b_l10429d := by
  have f0 : InstrSpec 0x10429d [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x10429d) (cmpR64R64Effect 0x10429d 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x10429d 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x10429d 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042a0) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1042a0 3 0xb9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l10429d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10429d :=
  Rest.liftedBlock (rest_l10429d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10429d x hx)

theorem rest_l1042a6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1042a6 bytes_l1042a6) (entryMap (live .l1042a6))
      20 0x1042a6 bytes_l1042a6 b_l1042a6 := by
  have f0 : InstrSpec 0x1042a6 [0x44, 0x0F, 0xB7, 0x54, 0x57, 0x0C] (LoadPre 0x1042a6 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xc)) s (0x1042a6 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1042a6 6 10 (.sib 7 (some 2) 1 (.d8 0xc)))
      [.gpr 7, .gpr 2] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x1042a6 6 10 (.sib 7 (some 2) 1 (.d8 0xc))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1042a6 0x44 (by decide) 2 (.sib 7 (some 2) 1 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1042ac [0x44, 0x89, 0xC1] (fun s => s.RIP = 0x1042ac) (movR32R32Effect 0x1042ac 3 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1042ac 3 1 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x1042ac 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1042af [0x66, 0x41, 0xD3, 0xCA] (fun s => s.RIP = 0x1042af) (rorR16ClEffect 0x1042af 4 10)
      [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rorR16ClEffect_footprint 0x1042af 4 10).toInstrSpec (ror_r16_cl_rex_effect_step 0x1042af 0x41 0xca (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1042b3 [0x41, 0x81, 0xE2, 0x11, 0x11, 0x00, 0x00] (fun s => s.RIP = 0x1042b3) (andR32Imm32Effect 0x1042b3 7 10 0x1111)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1042b3 7 10 0x1111).toInstrSpec (and_r32_imm32_rex_effect_step 0x1042b3 0x41 0xe2 0x1111 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1042ba [0x66, 0x46, 0x33, 0x14, 0x4F] (LoadPre 0x1042ba (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x1042ba + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x1042ba 5 10 (.sib 7 (some 9) 1 .none))
      [.gpr 10, .gpr 7, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1042ba 5 10 (.sib 7 (some 9) 1 .none)).toInstrSpec (xor_r16_m16_rex_effect_step 0x1042ba 0x46 (by decide) 2 (.sib 7 (some 9) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1042bf [0x43, 0x8D, 0x0C, 0x12] (fun s => s.RIP = 0x1042bf) (leaR32Effect 0x1042bf 4 1 (.sib 10 (some 10) 0 .none))
      [.gpr 10, .gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x1042bf 4 1 (.sib 10 (some 10) 0 .none)).toInstrSpec (lea_r32_rex_effect_step 0x1042bf 0x43 (by decide) 1 (.sib 10 (some 10) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1042c3 [0x81, 0xE1, 0xEE, 0xEE, 0xFF, 0xFF] (fun s => s.RIP = 0x1042c3) (andR32Imm32Effect 0x1042c3 6 1 0xffffeeee)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1042c3 6 1 0xffffeeee).toInstrSpec (and_r32_imm32_effect_step 0x1042c3 0xe1 0xffffeeee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1042c9 [0x46, 0x8D, 0x0C, 0x95, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1042c9) (leaR32Effect 0x1042c9 8 9 (.abs (some 10) 2 0x0))
      [.gpr 10] [] [.reg 9, .rip] :=
    (leaR32Effect_footprint 0x1042c9 8 9 (.abs (some 10) 2 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x1042c9 0x46 (by decide) 1 (.abs (some 10) 2 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1042d1 [0x41, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x1042d1) (andR32Imm32Effect 0x1042d1 7 9 0xffffcccc)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1042d1 7 9 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x1042d1 0x41 0xe1 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1042d8 [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x1042d8) (xorR32R32Effect 0x1042d8 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1042d8 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x1042d8 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1042db [0x42, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1042db) (leaR32Effect 0x1042db 8 1 (.abs (some 10) 3 0x0))
      [.gpr 10] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x1042db 8 1 (.abs (some 10) 3 0x0)).toInstrSpec (lea_r32_rex_effect_step 0x1042db 0x42 (by decide) 1 (.abs (some 10) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1042e3 [0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x1042e3) (andR32Imm32Effect 0x1042e3 6 1 0xffff8888)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1042e3 6 1 0xffff8888).toInstrSpec (and_r32_imm32_effect_step 0x1042e3 0xe1 0xffff8888 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1042e9 [0x44, 0x31, 0xD1] (fun s => s.RIP = 0x1042e9) (xorR32R32Effect 0x1042e9 3 1 10)
      [.gpr 1, .gpr 10] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1042e9 3 1 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1042e9 0x44 0xd1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1042ec [0x44, 0x31, 0xC9] (fun s => s.RIP = 0x1042ec) (xorR32R32Effect 0x1042ec 3 1 9)
      [.gpr 1, .gpr 9] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1042ec 3 1 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x1042ec 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1042ef [0x66, 0x89, 0x4C, 0x57, 0x0C] (StorePre 0x1042ef 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xc)) s (0x1042ef + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1042ef 5 1 (.sib 7 (some 2) 1 (.d8 0xc)))
      [.gpr 1, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x1042ef 5 1 (.sib 7 (some 2) 1 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x1042ef 1 (.sib 7 (some 2) 1 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1042f4 [0x48, 0x8D, 0x4A, 0x07] (fun s => s.RIP = 0x1042f4) (leaR64Effect 0x1042f4 1 (.base 2 (.d8 0x7)))
      [.gpr 2] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x1042f4 1 (.base 2 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x1042f4 0x48 (by decide) 1 (.base 2 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1042f8 [0x49, 0x89, 0xC9] (fun s => s.RIP = 0x1042f8) (movR64R64Effect 0x1042f8 9 1)
      [.gpr 1] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x1042f8 9 1).toInstrSpec (mov_r64_r64_effect_step 0x1042f8 0x49 0xc9 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x1042fb [0x49, 0x29, 0xC1] (fun s => s.RIP = 0x1042fb) (subR64R64Effect 0x1042fb 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1042fb 9 0).toInstrSpec (sub_r64_r64_effect_step 0x1042fb 0x49 0xc1 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1042fe [0x49, 0x39, 0xF1] (fun s => s.RIP = 0x1042fe) (cmpR64R64Effect 0x1042fe 9 6)
      [.gpr 9, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x1042fe 9 6).toInstrSpec (cmp_r64_r64_effect_step 0x1042fe 0x49 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042ac) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042af) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042b3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042ba) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042bf) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042c3) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042c9) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 67), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042d1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 69), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042d8) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042db) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042e3) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042e9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042ec) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042ef) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042f4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 71), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042f8) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 84), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042fb) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1042fe) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 0), (1, 82), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 86), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 88), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104301) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 90) (jcc_rel8_effect_step 0x104301 3 0x4a) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1042a6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1042a6 :=
  Rest.liftedBlock (rest_l1042a6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1042a6 x hx)

theorem rest_l104303 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104303 bytes_l104303) (entryMap (live .l104303))
      2 0x104303 bytes_l104303 b_l104303 := by
  have f0 : InstrSpec 0x104303 [0x48, 0x39, 0xF1] (fun s => s.RIP = 0x104303) (cmpR64R64Effect 0x104303 1 6)
      [.gpr 1, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x104303 1 6).toInstrSpec (cmp_r64_r64_effect_step 0x104303 0x48 0xf1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104306) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x104306 3 0x57) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l104303 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104303 :=
  Rest.liftedBlock (rest_l104303 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104303 x hx)

theorem rest_l104308 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104308 bytes_l104308) (entryMap (live .l104308))
      17 0x104308 bytes_l104308 b_l104308 := by
  have f0 : InstrSpec 0x104308 [0x0F, 0xB7, 0x44, 0x57, 0x0E] (LoadPre 0x104308 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xe)) s (0x104308 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x104308 5 0 (.sib 7 (some 2) 1 (.d8 0xe)))
      [.gpr 7, .gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x104308 5 0 (.sib 7 (some 2) 1 (.d8 0xe))).toInstrSpec (movzx_r32_m16_effect_step 0x104308 0 (.sib 7 (some 2) 1 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10430d [0x44, 0x89, 0xC1] (fun s => s.RIP = 0x10430d) (movR32R32Effect 0x10430d 3 1 8)
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10430d 3 1 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x10430d 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x104310 [0x66, 0xD3, 0xC8] (fun s => s.RIP = 0x104310) (rorR16ClEffect 0x104310 3 0)
      [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rorR16ClEffect_footprint 0x104310 3 0).toInstrSpec (ror_r16_cl_effect_step 0x104310 0xc8 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x104313 [0x25, 0x11, 0x11, 0x00, 0x00] (fun s => s.RIP = 0x104313) (andEaxImm32Effect 0x104313 0x1111)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x104313 0x1111).toInstrSpec (and_eax_imm32_effect_step 0x104313 0x1111) pre_rip
  have f4 : InstrSpec 0x104318 [0x66, 0x42, 0x33, 0x04, 0x4F] (LoadPre 0x104318 (fun s => AddrMode.addr (.sib 7 (some 9) 1 .none) s (0x104318 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x104318 5 0 (.sib 7 (some 9) 1 .none))
      [.gpr 0, .gpr 7, .gpr 9] [] [.reg 0, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x104318 5 0 (.sib 7 (some 9) 1 .none)).toInstrSpec (xor_r16_m16_rex_effect_step 0x104318 0x42 (by decide) 0 (.sib 7 (some 9) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10431d [0x8D, 0x0C, 0x00] (fun s => s.RIP = 0x10431d) (leaR32Effect 0x10431d 3 1 (.sib 0 (some 0) 0 .none))
      [.gpr 0, .gpr 0] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x10431d 3 1 (.sib 0 (some 0) 0 .none)).toInstrSpec (lea_r32_effect_step 0x10431d 1 (.sib 0 (some 0) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x104320 [0x81, 0xE1, 0xEE, 0xEE, 0xFF, 0xFF] (fun s => s.RIP = 0x104320) (andR32Imm32Effect 0x104320 6 1 0xffffeeee)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x104320 6 1 0xffffeeee).toInstrSpec (and_r32_imm32_effect_step 0x104320 0xe1 0xffffeeee (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x104326 [0x8D, 0x34, 0x85, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104326) (leaR32Effect 0x104326 7 6 (.abs (some 0) 2 0x0))
      [.gpr 0] [] [.reg 6, .rip] :=
    (leaR32Effect_footprint 0x104326 7 6 (.abs (some 0) 2 0x0)).toInstrSpec (lea_r32_effect_step 0x104326 6 (.abs (some 0) 2 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10432d [0x81, 0xE6, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x10432d) (andR32Imm32Effect 0x10432d 6 6 0xffffcccc)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10432d 6 6 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x10432d 0xe6 0xffffcccc (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x104333 [0x31, 0xCE] (fun s => s.RIP = 0x104333) (xorR32R32Effect 0x104333 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104333 2 6 1).toInstrSpec (xor_r32_r32_effect_step 0x104333 0xce (by decide)) pre_rip
  have f10 : InstrSpec 0x104335 [0x8D, 0x0C, 0xC5, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104335) (leaR32Effect 0x104335 7 1 (.abs (some 0) 3 0x0))
      [.gpr 0] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x104335 7 1 (.abs (some 0) 3 0x0)).toInstrSpec (lea_r32_effect_step 0x104335 1 (.abs (some 0) 3 0x0) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10433c [0x81, 0xE1, 0x88, 0x88, 0xFF, 0xFF] (fun s => s.RIP = 0x10433c) (andR32Imm32Effect 0x10433c 6 1 0xffff8888)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10433c 6 1 0xffff8888).toInstrSpec (and_r32_imm32_effect_step 0x10433c 0xe1 0xffff8888 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x104342 [0x31, 0xC1] (fun s => s.RIP = 0x104342) (xorR32R32Effect 0x104342 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104342 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x104342 0xc1 (by decide)) pre_rip
  have f13 : InstrSpec 0x104344 [0x31, 0xF1] (fun s => s.RIP = 0x104344) (xorR32R32Effect 0x104344 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x104344 2 1 6).toInstrSpec (xor_r32_r32_effect_step 0x104344 0xf1 (by decide)) pre_rip
  have f14 : InstrSpec 0x104346 [0x66, 0x89, 0x4C, 0x57, 0x0E] (StorePre 0x104346 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xe)) s (0x104346 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x104346 5 1 (.sib 7 (some 2) 1 (.d8 0xe)))
      [.gpr 1, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x104346 5 1 (.sib 7 (some 2) 1 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x104346 1 (.sib 7 (some 2) 1 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10434b [0x58] (PopPre 0x10434b) (popR64Effect 0x10434b 1 0)
      [.gpr 4] [] [.reg 0, .reg 4, .rip] :=
    (popR64Effect_footprint 0x10434b 1 0).toInstrSpec (pop_r64_effect_step 0x10434b 0x58 (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f16 : InstrSpec 0x10434c [0xC3] (RetPre 0x10434c) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x10434c).toInstrSpec (ret_effect_step 0x10434c) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10430d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104310) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104313) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104318) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10431d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104320) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104326) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 67), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10432d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 69), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104333) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 65), (2, 2), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104335) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 73), (2, 2), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10433c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104342) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 61), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104344) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 61), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104346) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 61), (1, 79), (2, 2), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10434b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 83) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 84) (ρ' := [(0, 82), (1, 79), (2, 2), (3, 3), (4, 83), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10434c) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 86) f16 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 87) (ρ' := [(0, 82), (1, 79), (2, 2), (3, 3), (4, 86), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f16 (by decide) rfl rfl rfl (by decide)

theorem block_l104308 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104308 :=
  Rest.liftedBlock (rest_l104308 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104308 x hx)

theorem rest_l10434d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10434d bytes_l10434d) (entryMap (live .l10434d))
      3 0x10434d bytes_l10434d b_l10434d := by
  have f0 : InstrSpec 0x10434d [0x4C, 0x89, 0xCF] (fun s => s.RIP = 0x10434d) (movR64R64Effect 0x10434d 7 9)
      [.gpr 9] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10434d 7 9).toInstrSpec (mov_r64_r64_effect_step 0x10434d 0x4c 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104350 [0x48, 0xC7, 0xC2, 0x28, 0x10, 0x20, 0x00] (fun s => s.RIP = 0x104350) (movR64Imm32Effect 0x104350 2 0x201028)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x104350 2 0x201028).toInstrSpec (mov_r64_imm32_effect_step 0x104350 0x48 0xc2 (by decide) (by decide) (by decide) 0x201028) pre_rip
  have f2 : InstrSpec 0x104357 [0xE8, 0xDB, 0xF4, 0xFF, 0xFF] (PushPre 0x104357 5) (callEffect (fun _ => 0x103837) 0x10435c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104357 0x103837 0x10435c).toInstrSpec (call_rel32_effect_step 0x104357 0xfffff4db (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (5, 5), (6, 6), (7, 53), (9, 9)]) (p' := 0x104350) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (4, 4), (5, 5), (6, 6), (7, 53), (9, 9)]) (p' := 0x104357) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53), (9, 9)]) (p' := 0x103837) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10434d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10434d :=
  Rest.liftedBlock (rest_l10434d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10434d x hx)

theorem rest_l10435c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10435c bytes_l10435c) (entryMap (live .l10435c))
      1 0x10435c bytes_l10435c b_l10435c := by
  have f0 : InstrSpec 0x10435c [0x48, 0x89, 0xD1] (fun s => s.RIP = 0x10435c) (movR64R64Effect 0x10435c 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x10435c 1 2).toInstrSpec (mov_r64_r64_effect_step 0x10435c 0x48 0xd1 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x10435f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l10435c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10435c :=
  Rest.liftedBlock (rest_l10435c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10435c x hx)

theorem rest_l10435f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10435f bytes_l10435f) (entryMap (live .l10435f))
      3 0x10435f bytes_l10435f b_l10435f := by
  have f0 : InstrSpec 0x10435f [0x48, 0x89, 0xCF] (fun s => s.RIP = 0x10435f) (movR64R64Effect 0x10435f 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10435f 7 1).toInstrSpec (mov_r64_r64_effect_step 0x10435f 0x48 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x104362 [0x48, 0xC7, 0xC2, 0x40, 0x10, 0x20, 0x00] (fun s => s.RIP = 0x104362) (movR64Imm32Effect 0x104362 2 0x201040)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x104362 2 0x201040).toInstrSpec (mov_r64_imm32_effect_step 0x104362 0x48 0xc2 (by decide) (by decide) (by decide) 0x201040) pre_rip
  have f2 : InstrSpec 0x104369 [0xE8, 0xC9, 0xF4, 0xFF, 0xFF] (PushPre 0x104369 5) (callEffect (fun _ => 0x103837) 0x10436e)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104369 0x103837 0x10436e).toInstrSpec (call_rel32_effect_step 0x104369 0xfffff4c9 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 1), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x104362) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x104369) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(1, 1), (2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x103837) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l10435f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10435f :=
  Rest.liftedBlock (rest_l10435f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10435f x hx)

theorem rest_l10436e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10436e bytes_l10436e) (entryMap (live .l10436e))
      1 0x10436e bytes_l10436e b_l10436e := by
  have f0 : InstrSpec 0x10436e [0x66, 0x90] (fun s => s.RIP = 0x10436e) (fun _ => nopEffect 0x10436e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10436e 2).toInstrSpec (nop_66_effect_step 0x10436e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104370) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l10436e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10436e :=
  Rest.liftedBlock (rest_l10436e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10436e x hx)

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

theorem_by block_l104010_eval :
    program.runBlock (dialect code) ⟨.l104010, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104020_eval :
    program.runBlock (dialect code) ⟨.l104020, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104029_eval :
    program.runBlock (dialect code) ⟨.l104029, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10408b_eval :
    program.runBlock (dialect code) ⟨.l10408b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104094_eval :
    program.runBlock (dialect code) ⟨.l104094, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1040f5_eval :
    program.runBlock (dialect code) ⟨.l1040f5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1040fe_eval :
    program.runBlock (dialect code) ⟨.l1040fe, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10415f_eval :
    program.runBlock (dialect code) ⟨.l10415f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104168_eval :
    program.runBlock (dialect code) ⟨.l104168, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1041c9_eval :
    program.runBlock (dialect code) ⟨.l1041c9, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1041d2_eval :
    program.runBlock (dialect code) ⟨.l1041d2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104233_eval :
    program.runBlock (dialect code) ⟨.l104233, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10423c_eval :
    program.runBlock (dialect code) ⟨.l10423c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10429d_eval :
    program.runBlock (dialect code) ⟨.l10429d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1042a6_eval :
    program.runBlock (dialect code) ⟨.l1042a6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104303_eval :
    program.runBlock (dialect code) ⟨.l104303, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104308_eval :
    program.runBlock (dialect code) ⟨.l104308, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10434d_eval :
    program.runBlock (dialect code) ⟨.l10434d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10435c_eval :
    program.runBlock (dialect code) ⟨.l10435c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10435f_eval :
    program.runBlock (dialect code) ⟨.l10435f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10436e_eval :
    program.runBlock (dialect code) ⟨.l10436e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
