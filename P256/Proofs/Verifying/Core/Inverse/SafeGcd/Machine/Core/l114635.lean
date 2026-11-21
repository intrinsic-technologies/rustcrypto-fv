import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l114635 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1125e5 bytes_l114635) (entryMap (live .l114635))
      12 0x1125e5 bytes_l114635 b_l114635 := by
  have f0 : InstrSpec 0x1125e5 [0x49, 0x89, 0xC8] (fun s => s.RIP = 0x1125e5) (movR64R64Effect 0x1125e5 8 1)
      [.gpr 1] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x1125e5 8 1).toInstrSpec (mov_r64_r64_effect_step 0x1125e5 0x49 0xc8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1125e8 [0x49, 0x29, 0xC0] (fun s => s.RIP = 0x1125e8) (subR64R64Effect 0x1125e8 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1125e8 8 0).toInstrSpec (sub_r64_r64_effect_step 0x1125e8 0x49 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1125eb [0xB8, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1125eb) (movR32Imm32Effect 0x1125eb 5 0 0x2)
      [] [] [.reg 0, .rip] :=
    (movR32Imm32Effect_footprint 0x1125eb 5 0 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x1125eb 0xb8 (by decide) 0x2) pre_rip
  have f3 : InstrSpec 0x1125f0 [0x4C, 0x29, 0xE0] (fun s => s.RIP = 0x1125f0) (subR64R64Effect 0x1125f0 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1125f0 0 12).toInstrSpec (sub_r64_r64_effect_step 0x1125f0 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1125f3 [0x49, 0x89, 0xF5] (fun s => s.RIP = 0x1125f3) (movR64R64Effect 0x1125f3 13 6)
      [.gpr 6] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x1125f3 13 6).toInstrSpec (mov_r64_r64_effect_step 0x1125f3 0x49 0xf5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1125f6 [0x49, 0x29, 0xDD] (fun s => s.RIP = 0x1125f6) (subR64R64Effect 0x1125f6 13 3)
      [.gpr 13, .gpr 3] [] [.reg 13, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1125f6 13 3).toInstrSpec (sub_r64_r64_effect_step 0x1125f6 0x49 0xdd (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1125f9 [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x1125f9) (movR64R64Effect 0x1125f9 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x1125f9 14 7).toInstrSpec (mov_r64_r64_effect_step 0x1125f9 0x49 0xfe (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1125fc [0x4D, 0x29, 0xFE] (fun s => s.RIP = 0x1125fc) (subR64R64Effect 0x1125fc 14 15)
      [.gpr 14, .gpr 15] [] [.reg 14, .flags, .rip] :=
    (subR64R64Effect_footprint 0x1125fc 14 15).toInstrSpec (sub_r64_r64_effect_step 0x1125fc 0x4d 0xfe (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1125ff [0x49, 0x89, 0xFF] (fun s => s.RIP = 0x1125ff) (movR64R64Effect 0x1125ff 15 7)
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x1125ff 15 7).toInstrSpec (mov_r64_r64_effect_step 0x1125ff 0x49 0xff (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112602 [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x112602) (movR64R64Effect 0x112602 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x112602 3 6).toInstrSpec (mov_r64_r64_effect_step 0x112602 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112605 [0x49, 0x89, 0xC4] (fun s => s.RIP = 0x112605) (movR64R64Effect 0x112605 12 0)
      [.gpr 0] [] [.reg 12, .rip] :=
    (movR64R64Effect_footprint 0x112605 12 0).toInstrSpec (mov_r64_r64_effect_step 0x112605 0x49 0xc4 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112608 [0x48, 0x89, 0xC8] (fun s => s.RIP = 0x112608) (movR64R64Effect 0x112608 0 1)
      [.gpr 1] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x112608 0 1).toInstrSpec (mov_r64_r64_effect_step 0x112608 0x48 0xc8 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125e8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125eb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125f0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125f3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125f6) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 63), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125f9) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 63), (14, 65), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125fc) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 63), (14, 67), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1125ff) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 63), (14, 67), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x112602) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 71), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 63), (14, 67), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x112605) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 59), (1, 1), (2, 2), (3, 71), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 73), (13, 63), (14, 67), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x112608) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 75), (1, 1), (2, 2), (3, 71), (4, 4), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 73), (13, 63), (14, 67), (15, 69), (22, 22), (39, 39), (51, 51)]) (p' := 0x11260b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l114635 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l114635 :=
  Rest.liftedBlock (rest_l114635 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l114635 x hx)

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

theorem_by block_l114635_eval :
    program.runBlock (dialect code) ⟨.l114635, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
