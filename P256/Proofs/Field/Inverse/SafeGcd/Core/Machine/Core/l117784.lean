import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l117784 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111ca4 bytes_l117784) (entryMap (live .l117784))
      4 0x111ca4 bytes_l117784 b_l117784 := by
  have f0 : InstrSpec 0x111ca4 [0xBD, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111ca4) (movR32Imm32Effect 0x111ca4 5 5 0x1)
      [] [] [.reg 5, .rip] :=
    (movR32Imm32Effect_footprint 0x111ca4 5 5 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x111ca4 0xbd (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x111ca9 [0xBA, 0x4F, 0x02, 0x00, 0x00] (fun s => s.RIP = 0x111ca9) (movR32Imm32Effect 0x111ca9 5 2 0x24f)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x111ca9 5 2 0x24f).toInstrSpec (mov_r32_imm32_effect_step 0x111ca9 0xba (by decide) 0x24f) pre_rip
  have f2 : InstrSpec 0x111cae [0x4C, 0x8D, 0x6C, 0x24, 0x08] (fun s => s.RIP = 0x111cae) (leaR64Effect 0x111cae 13 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (leaR64Effect_footprint 0x111cae 13 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x111cae 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 53), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111ca9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 53), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111cae) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (5, 53), (9, 9), (10, 10), (11, 11), (13, 57), (14, 14), (22, 22), (39, 39), (51, 51)]) (p' := 0x111cb3) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 59) (jmp_rel32_effect_step 0x111cb3 0x262 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l117784 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l117784 :=
  Rest.liftedBlock (rest_l117784 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l117784 x hx)

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

theorem_by block_l117784_eval :
    program.runBlock (dialect code) ⟨.l117784, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
