import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l114574 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112524 bytes_l114574) (entryMap (live .l114574))
      14 0x112524 bytes_l114574 b_l114574 := by
  have f0 : InstrSpec 0x112524 [0x89, 0xF0] (fun s => s.RIP = 0x112524) (movR32R32Effect 0x112524 2 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x112524 2 0 6).toInstrSpec (mov_r32_r32_effect_step 0x112524 0xf0 (by decide)) pre_rip
  have f1 : InstrSpec 0x112526 [0xF7, 0xD0] (fun s => s.RIP = 0x112526) (notR32Effect 0x112526 2 0)
      [.gpr 0] [] [.reg 0, .rip] :=
    (notR32Effect_footprint 0x112526 2 0).toInstrSpec (not_r32_effect_step 0x112526 0xd0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112528 [0x8D, 0x4E, 0xC2] (fun s => s.RIP = 0x112528) (leaR32Effect 0x112528 3 1 (.base 6 (.d8 0xc2)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x112528 3 1 (.base 6 (.d8 0xc2))).toInstrSpec (lea_r32_effect_step 0x112528 1 (.base 6 (.d8 0xc2)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11252b [0x21, 0xC1] (fun s => s.RIP = 0x11252b) (andR32R32Effect 0x11252b 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR32R32Effect_footprint 0x11252b 2 1 0).toInstrSpec (and_r32_r32_effect_step 0x11252b 0xc1 (by decide)) pre_rip
  have f4 : InstrSpec 0x11252d [0xC1, 0xE9, 0x1F] (fun s => s.RIP = 0x11252d) (shrR32Effect 0x11252d 3 1 31)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x11252d 3 1 31).toInstrSpec (shr_r32_imm8_effect_step 0x11252d 0xe9 0x1f (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x112530 [0x88, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x112530 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x112530 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x112530 7 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x112530 7 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m8_r8_effect_step 0x112530 1 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x112537 [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x112537) (leaR64Effect 0x112537 7 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x112537 7 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (lea_r64_effect_step 0x112537 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11253f [0x0F, 0xB6, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x11253f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11253f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x11253f 8 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x11253f 8 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (movzx_r32_m8_effect_step 0x11253f 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x112547 [0xF7, 0xD8] (fun s => s.RIP = 0x112547) (negR32Effect 0x112547 2 0)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (negR32Effect_footprint 0x112547 2 0).toInstrSpec (neg_r32_effect_step 0x112547 0xd8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112549 [0x48, 0x89, 0xB4, 0x24, 0x50, 0x01, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112549 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x112549 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112549 6 (.sib 4 none 0 (.d32 0x150)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112549 6 (.sib 4 none 0 (.d32 0x150))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112549 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f10 : InstrSpec 0x112551 [0x41, 0x89, 0xF1] (fun s => s.RIP = 0x112551) (movR32R32Effect 0x112551 3 9 6)
      [.gpr 6] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x112551 3 9 6).toInstrSpec (mov_r32_r32_rex_effect_step 0x112551 0x41 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112554 [0x41, 0x83, 0xF1, 0x3E] (fun s => s.RIP = 0x112554) (xorR32Imm8Effect 0x112554 4 9 0x3e)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x112554 4 9 0x3e).toInstrSpec (xor_r32_imm8_rex_effect_step 0x112554 0x41 0xf1 0x3e (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x112558 [0x41, 0x21, 0xC1] (fun s => s.RIP = 0x112558) (andR32R32Effect 0x112558 3 9 0)
      [.gpr 9, .gpr 0] [] [.reg 9, .flags, .rip] :=
    (andR32R32Effect_footprint 0x112558 3 9 0).toInstrSpec (and_r32_r32_rex_effect_step 0x112558 0x41 0xc1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11255b [0x41, 0x83, 0xF1, 0x3E] (fun s => s.RIP = 0x11255b) (xorR32Imm8Effect 0x11255b 4 9 0x3e)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (xorR32Imm8Effect_footprint 0x11255b 4 9 0x3e).toInstrSpec (xor_r32_imm8_rex_effect_step 0x11255b 0x41 0xf1 0x3e (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112526) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (4, 4), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112528) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (2, 2), (4, 4), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11252b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 59), (2, 2), (4, 4), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11252d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 55), (1, 61), (2, 2), (4, 4), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112530) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 55), (1, 61), (2, 2), (4, 4), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112537) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 55), (1, 61), (2, 2), (4, 4), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11253f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 61), (2, 2), (4, 4), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112547) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112549) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112551) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (9, 70), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112554) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112558) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (9, 74), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11255b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 77) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 78) (ρ' := [(0, 67), (1, 61), (2, 2), (4, 4), (6, 6), (9, 76), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 77), (22, 22), (39, 39), (51, 51)]) (p' := 0x11255f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 79) (by decide) rfl

theorem block_l114574 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l114574 :=
  Rest.liftedBlock (rest_l114574 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l114574 x hx)

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

theorem_by block_l114574_eval :
    program.runBlock (dialect code) ⟨.l114574, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
