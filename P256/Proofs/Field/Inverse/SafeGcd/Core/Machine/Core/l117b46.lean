import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117b46 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112066 bytes_l117b46) (entryMap (live .l117b46))
      17 0x112066 bytes_l117b46 b_l117b46 := by
  have f0 : InstrSpec 0x112066 [0x4D, 0x89, 0xF7] (fun s => s.RIP = 0x112066) (movR64R64Effect 0x112066 15 14)
      [.gpr 14] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x112066 15 14).toInstrSpec (mov_r64_r64_effect_step 0x112066 0x4d 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x112069 [0x49, 0x31, 0xFF] (fun s => s.RIP = 0x112069) (xorR64R64Effect 0x112069 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x112069 15 7).toInstrSpec (xor_r64_r64_effect_step 0x112069 0x49 0xff (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11206c [0x4D, 0x21, 0xDF] (fun s => s.RIP = 0x11206c) (andR64R64Effect 0x11206c 15 11)
      [.gpr 15, .gpr 11] [] [.reg 15, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11206c 15 11).toInstrSpec (and_r64_r64_effect_step 0x11206c 0x4d 0xdf (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11206f [0x44, 0x88, 0x54, 0x24, 0x08] (StorePre 0x11206f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11206f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11206f 5 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11206f 5 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11206f 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x112074 [0x44, 0x0F, 0xB6, 0x54, 0x24, 0x08] (LoadPre 0x112074 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112074 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x112074 6 10 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M8Effect_footprint 0x112074 6 10 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x112074 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11207a [0x49, 0xF7, 0xDA] (fun s => s.RIP = 0x11207a) (negR64Effect 0x11207a 10)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (negR64Effect_footprint 0x11207a 10).toInstrSpec (neg_r64_effect_step 0x11207a 0x49 0xda (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11207d [0x4C, 0x89, 0xE3] (fun s => s.RIP = 0x11207d) (movR64R64Effect 0x11207d 3 12)
      [.gpr 12] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x11207d 3 12).toInstrSpec (mov_r64_r64_effect_step 0x11207d 0x4c 0xe3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112080 [0x48, 0x31, 0xF3] (fun s => s.RIP = 0x112080) (xorR64R64Effect 0x112080 3 6)
      [.gpr 3, .gpr 6] [] [.reg 3, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x112080 3 6).toInstrSpec (xor_r64_r64_effect_step 0x112080 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x112083 [0x4C, 0x21, 0xD3] (fun s => s.RIP = 0x112083) (andR64R64Effect 0x112083 3 10)
      [.gpr 3, .gpr 10] [] [.reg 3, .flags, .rip] :=
    (andR64R64Effect_footprint 0x112083 3 10).toInstrSpec (and_r64_r64_effect_step 0x112083 0x4c 0xd3 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112086 [0x49, 0x89, 0xFA] (fun s => s.RIP = 0x112086) (movR64R64Effect 0x112086 10 7)
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR64R64Effect_footprint 0x112086 10 7).toInstrSpec (mov_r64_r64_effect_step 0x112086 0x49 0xfa (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112089 [0x49, 0xF7, 0xDA] (fun s => s.RIP = 0x112089) (negR64Effect 0x112089 10)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (negR64Effect_footprint 0x112089 10).toInstrSpec (neg_r64_effect_step 0x112089 0x49 0xda (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11208c [0x44, 0x88, 0x4C, 0x24, 0x08] (StorePre 0x11208c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11208c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11208c 5 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11208c 5 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11208c 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x112091 [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x08] (LoadPre 0x112091 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112091 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x112091 6 11 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movzxR32M8Effect_footprint 0x112091 6 11 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x112091 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x112097 [0x49, 0xF7, 0xDB] (fun s => s.RIP = 0x112097) (negR64Effect 0x112097 11)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (negR64Effect_footprint 0x112097 11).toInstrSpec (neg_r64_effect_step 0x112097 0x49 0xdb (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x11209a [0x49, 0x31, 0xFA] (fun s => s.RIP = 0x11209a) (xorR64R64Effect 0x11209a 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x11209a 10 7).toInstrSpec (xor_r64_r64_effect_step 0x11209a 0x49 0xfa (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11209d [0x4D, 0x21, 0xDA] (fun s => s.RIP = 0x11209d) (andR64R64Effect 0x11209d 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11209d 10 11).toInstrSpec (and_r64_r64_effect_step 0x11209d 0x4d 0xda (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1120a0 [0x49, 0x31, 0xFF] (fun s => s.RIP = 0x1120a0) (xorR64R64Effect 0x1120a0 15 7)
      [.gpr 15, .gpr 7] [] [.reg 15, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1120a0 15 7).toInstrSpec (xor_r64_r64_effect_step 0x1120a0 0x49 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (51, 51)]) (p' := 0x112069) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (51, 51)]) (p' := 0x11206c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x11206f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112074) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 60), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x11207a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 62), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x11207d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 64), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 62), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112080) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 66), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 62), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112083) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 62), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112086) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 70), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112089) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 72), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x11208c) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 72), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112091) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 72), (11, 75), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x112097) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 72), (11, 77), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x11209a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 79), (11, 77), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x11209d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 81), (11, 77), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120a0) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 81), (11, 77), (12, 12), (13, 13), (14, 14), (15, 83), (22, 22), (39, 39), (51, 51)]) (p' := 0x1120a3) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 85) (by decide) rfl

theorem block_l117b46 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117b46 :=
  Rest.liftedBlock (rest_l117b46 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117b46 x hx)

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

theorem_by block_l117b46_eval :
    program.runBlock (dialect code) ⟨.l117b46, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
