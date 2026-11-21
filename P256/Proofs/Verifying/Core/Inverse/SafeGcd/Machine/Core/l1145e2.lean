import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1145e2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112592 bytes_l1145e2) (entryMap (live .l1145e2))
      15 0x112592 bytes_l1145e2 b_l1145e2 := by
  have f0 : InstrSpec 0x112592 [0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x112592) (movR64Imm64Effect 0x112592 8 0x7fffffffffffffff)
      [] [] [.reg 8, .rip] :=
    (movR64Imm64Effect_footprint 0x112592 8 0x7fffffffffffffff).toInstrSpec (mov_r64_imm64_effect_step 0x112592 0x49 0xb8 (by decide) (by decide) 0x7fffffffffffffff) pre_rip
  have f1 : InstrSpec 0x11259c [0x4C, 0x21, 0xC2] (fun s => s.RIP = 0x11259c) (andR64R64Effect 0x11259c 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (andR64R64Effect_footprint 0x11259c 2 8).toInstrSpec (and_r64_r64_effect_step 0x11259c 0x4c 0xc2 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11259f [0x48, 0x89, 0xD7] (fun s => s.RIP = 0x11259f) (movR64R64Effect 0x11259f 7 2)
      [.gpr 2] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11259f 7 2).toInstrSpec (mov_r64_r64_effect_step 0x11259f 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1125a2 [0x48, 0xF7, 0xDF] (fun s => s.RIP = 0x1125a2) (negR64Effect 0x1125a2 7)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (negR64Effect_footprint 0x1125a2 7).toInstrSpec (neg_r64_effect_step 0x1125a2 0x48 0xdf (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1125a5 [0x48, 0x31, 0xD7] (fun s => s.RIP = 0x1125a5) (xorR64R64Effect 0x1125a5 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1125a5 7 2).toInstrSpec (xor_r64_r64_effect_step 0x1125a5 0x48 0xd7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1125a8 [0x48, 0xF7, 0xD9] (fun s => s.RIP = 0x1125a8) (negR64Effect 0x1125a8 1)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (negR64Effect_footprint 0x1125a8 1).toInstrSpec (neg_r64_effect_step 0x1125a8 0x48 0xd9 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1125ab [0x48, 0x21, 0xF9] (fun s => s.RIP = 0x1125ab) (andR64R64Effect 0x1125ab 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1125ab 1 7).toInstrSpec (and_r64_r64_effect_step 0x1125ab 0x48 0xf9 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1125ae [0x48, 0x31, 0xD1] (fun s => s.RIP = 0x1125ae) (xorR64R64Effect 0x1125ae 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1125ae 1 2).toInstrSpec (xor_r64_r64_effect_step 0x1125ae 0x48 0xd1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1125b1 [0x4C, 0x21, 0xC6] (fun s => s.RIP = 0x1125b1) (andR64R64Effect 0x1125b1 6 8)
      [.gpr 6, .gpr 8] [] [.reg 6, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1125b1 6 8).toInstrSpec (and_r64_r64_effect_step 0x1125b1 0x4c 0xc6 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1125b4 [0x48, 0x89, 0xF2] (fun s => s.RIP = 0x1125b4) (movR64R64Effect 0x1125b4 2 6)
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64R64Effect_footprint 0x1125b4 2 6).toInstrSpec (mov_r64_r64_effect_step 0x1125b4 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1125b7 [0x48, 0xF7, 0xDA] (fun s => s.RIP = 0x1125b7) (negR64Effect 0x1125b7 2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (negR64Effect_footprint 0x1125b7 2).toInstrSpec (neg_r64_effect_step 0x1125b7 0x48 0xda (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1125ba [0x48, 0x31, 0xF2] (fun s => s.RIP = 0x1125ba) (xorR64R64Effect 0x1125ba 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1125ba 2 6).toInstrSpec (xor_r64_r64_effect_step 0x1125ba 0x48 0xf2 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1125bd [0x48, 0xF7, 0xD8] (fun s => s.RIP = 0x1125bd) (negR64Effect 0x1125bd 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR64Effect_footprint 0x1125bd 0).toInstrSpec (neg_r64_effect_step 0x1125bd 0x48 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1125c0 [0x48, 0x21, 0xD0] (fun s => s.RIP = 0x1125c0) (andR64R64Effect 0x1125c0 0 2)
      [.gpr 0, .gpr 2] [] [.reg 0, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1125c0 0 2).toInstrSpec (and_r64_r64_effect_step 0x1125c0 0x48 0xd0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x1125c3 [0x48, 0x31, 0xF0] (fun s => s.RIP = 0x1125c3) (xorR64R64Effect 0x1125c3 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (xorR64R64Effect_footprint 0x1125c3 0 6).toInstrSpec (xor_r64_r64_effect_step 0x1125c3 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11259c) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (6, 6), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11259f) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (6, 6), (7, 57), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125a2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (6, 6), (7, 59), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125a5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 55), (4, 4), (6, 6), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125a8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 55), (4, 4), (6, 6), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125ab) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 55), (4, 4), (6, 6), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125ae) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 55), (4, 4), (6, 6), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125b1) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 67), (2, 55), (4, 4), (6, 69), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125b4) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 67), (2, 71), (4, 4), (6, 69), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125b7) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 67), (2, 73), (4, 4), (6, 69), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125ba) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 67), (2, 75), (4, 4), (6, 69), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125bd) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (1, 67), (2, 75), (4, 4), (6, 69), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125c0) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 67), (2, 75), (4, 4), (6, 69), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125c3) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 67), (2, 75), (4, 4), (6, 69), (7, 61), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125c6) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 83) (by decide) rfl

theorem block_l1145e2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1145e2 :=
  Rest.liftedBlock (rest_l1145e2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1145e2 x hx)

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

theorem_by block_l1145e2_eval :
    program.runBlock (dialect code) ⟨.l1145e2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
