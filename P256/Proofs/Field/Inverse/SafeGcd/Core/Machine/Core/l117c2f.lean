import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117c2f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11214f bytes_l117c2f) (entryMap (live .l117c2f))
      16 0x11214f bytes_l117c2f b_l117c2f := by
  have f0 : InstrSpec 0x11214f [0x48, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x11214f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11214f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11214f 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11214f 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x11214f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x112154 [0x48, 0x83, 0xF0, 0x01] (fun s => s.RIP = 0x112154) (xorR64Imm8Effect 0x112154 0 0x1)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR64Imm8Effect_footprint 0x112154 0 0x1).toInstrSpec (xor_r64_imm8_effect_step 0x112154 0x48 0xf0 0x1 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112158 [0x48, 0x0B, 0x44, 0x24, 0x60] (LoadPre 0x112158 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x112158 + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x112158 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x112158 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (or_r64_m64_effect_step 0x112158 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11215d [0x48, 0x0B, 0x44, 0x24, 0x68] (LoadPre 0x11215d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x11215d + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x11215d 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x11215d 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (or_r64_m64_effect_step 0x11215d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112162 [0x48, 0x0B, 0x44, 0x24, 0x70] (LoadPre 0x112162 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x112162 + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x112162 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x112162 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (or_r64_m64_effect_step 0x112162 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x112167 [0x0F, 0x94, 0xC0] (fun s => s.RIP = 0x112167) (atFlags (condHolds 4) (setccR8Effect 0x112167 3 0))
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 0, .rip] :=
    (setccR8Effect_footprint 0x112167 3 0 4).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x112167 4 0xc0 (by decide) (by decide) c)) pre_rip
  have f6 : InstrSpec 0x11216a [0x20, 0xD8] (fun s => s.RIP = 0x11216a) (andR8R8Effect 0x11216a 2 0 3)
      [.gpr 0, .gpr 3] [] [.reg 0, .flags, .rip] :=
    (andR8R8Effect_footprint 0x11216a 2 0 3).toInstrSpec (and_r8_r8_effect_step 0x11216a 0xd8 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x11216c [0x41, 0x88, 0x46, 0x20] (StorePre 0x11216c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x11216c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11216c 4 0 (.base 14 (.d8 0x20)))
      [.gpr 0, .gpr 14] [] [.rip] :=
    (movM8R8Effect_footprint 0x11216c 4 0 (.base 14 (.d8 0x20))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11216c 0x41 (by decide) 0 (.base 14 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x112170 [0x48, 0x81, 0xC4, 0x58, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x112170) (addR64Imm32Effect 0x112170 4 0x158)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x112170 4 0x158).toInstrSpec (add_r64_imm32_effect_step 0x112170 0x48 0xc4 0x158 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112177 [0x5B] (PopPre 0x112177) (popR64Effect 0x112177 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x112177 1 3).toInstrSpec (pop_r64_effect_step 0x112177 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f10 : InstrSpec 0x112178 [0x41, 0x5C] (PopPre 0x112178) (popR64Effect 0x112178 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x112178 2 12).toInstrSpec (pop_r64_rex_effect_step 0x112178 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f11 : InstrSpec 0x11217a [0x41, 0x5D] (PopPre 0x11217a) (popR64Effect 0x11217a 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11217a 2 13).toInstrSpec (pop_r64_rex_effect_step 0x11217a 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f12 : InstrSpec 0x11217c [0x41, 0x5E] (PopPre 0x11217c) (popR64Effect 0x11217c 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11217c 2 14).toInstrSpec (pop_r64_rex_effect_step 0x11217c 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x11217e [0x41, 0x5F] (PopPre 0x11217e) (popR64Effect 0x11217e 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x11217e 2 15).toInstrSpec (pop_r64_rex_effect_step 0x11217e 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x112180 [0x5D] (PopPre 0x112180) (popR64Effect 0x112180 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x112180 1 5).toInstrSpec (pop_r64_effect_step 0x112180 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x112181 [0xC3] (RetPre 0x112181) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x112181).toInstrSpec (ret_effect_step 0x112181) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (3, 3), (4, 4), (8, 8), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112154) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (3, 3), (4, 4), (8, 8), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112158) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (2, 2), (3, 3), (4, 4), (8, 8), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11215d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (2, 2), (3, 3), (4, 4), (8, 8), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112162) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 61), (2, 2), (3, 3), (4, 4), (8, 8), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x112167) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (2, 2), (3, 3), (4, 4), (8, 8), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (51, 51)]) (p' := 0x11216a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 66), (2, 2), (3, 3), (4, 4), (8, 8), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11216c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 66), (2, 2), (3, 3), (4, 4), (8, 8), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112170) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 66), (2, 2), (3, 3), (4, 69), (8, 8), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112177) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 72) f9 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 73) (ρ' := [(0, 66), (2, 2), (3, 71), (4, 72), (8, 8), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x112178) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 75) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 76) (ρ' := [(0, 66), (2, 2), (3, 71), (4, 75), (8, 8), (10, 10), (11, 11), (12, 74), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11217a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 78) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 79) (ρ' := [(0, 66), (2, 2), (3, 71), (4, 78), (8, 8), (10, 10), (11, 11), (12, 74), (13, 77), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x11217c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f12 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 81) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 82) (ρ' := [(0, 66), (2, 2), (3, 71), (4, 81), (8, 8), (10, 10), (11, 11), (12, 74), (13, 77), (14, 80), (22, 22), (39, 39), (51, 51)]) (p' := 0x11217e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f13 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 84) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 85) (ρ' := [(0, 66), (2, 2), (3, 71), (4, 84), (8, 8), (10, 10), (11, 11), (12, 74), (13, 77), (14, 80), (15, 83), (22, 22), (39, 39), (51, 51)]) (p' := 0x112180) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f14 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 87) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 88) (ρ' := [(0, 66), (2, 2), (3, 71), (4, 87), (5, 86), (8, 8), (10, 10), (11, 11), (12, 74), (13, 77), (14, 80), (15, 83), (22, 22), (39, 39), (51, 51)]) (p' := 0x112181) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f15 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 90) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 91) (ρ' := [(0, 66), (2, 2), (3, 71), (4, 90), (5, 86), (8, 8), (10, 10), (11, 11), (12, 74), (13, 77), (14, 80), (15, 83), (22, 22), (39, 39), (51, 51)]) f15 (by decide) rfl rfl rfl (by decide)

theorem block_l117c2f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117c2f :=
  Rest.liftedBlock (rest_l117c2f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117c2f x hx)

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

theorem_by block_l117c2f_eval :
    program.runBlock (dialect code) ⟨.l117c2f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
