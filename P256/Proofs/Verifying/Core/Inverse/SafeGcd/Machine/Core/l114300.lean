import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l114300 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1122b0 bytes_l114300) (entryMap (live .l114300))
      4 0x1122b0 bytes_l114300 b_l114300 := by
  have f0 : InstrSpec 0x1122b0 [0x41, 0xBE, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1122b0) (movR32Imm32Effect 0x1122b0 6 14 0x1)
      [] [] [.reg 14, .rip] :=
    (movR32Imm32Effect_footprint 0x1122b0 6 14 0x1).toInstrSpec (mov_r32_imm32_rex_effect_step 0x1122b0 0x41 0xbe (by decide) (by decide) 0x1) pre_rip
  have f1 : InstrSpec 0x1122b6 [0x45, 0x31, 0xED] (fun s => s.RIP = 0x1122b6) (xorR32R32Effect 0x1122b6 3 13 13)
      [.gpr 13, .gpr 13] [] [.reg 13, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1122b6 3 13 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1122b6 0x45 0xed (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1122b9 [0x45, 0x31, 0xFF] (fun s => s.RIP = 0x1122b9) (xorR32R32Effect 0x1122b9 3 15 15)
      [.gpr 15, .gpr 15] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1122b9 3 15 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x1122b9 0x45 0xff (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1122bc [0xBB, 0x01, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1122bc) (movR32Imm32Effect 0x1122bc 5 3 0x1)
      [] [] [.reg 3, .rip] :=
    (movR32Imm32Effect_footprint 0x1122bc 5 3 0x1).toInstrSpec (mov_r32_imm32_effect_step 0x1122bc 0xbb (by decide) 0x1) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1122b6) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1122b9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 53), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x1122bc) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(3, 59), (4, 4), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 53), (15, 57), (22, 22), (39, 39), (51, 51)]) (p' := 0x1122c1) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l114300 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l114300 :=
  Rest.liftedBlock (rest_l114300 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l114300 x hx)

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

theorem_by block_l114300_eval :
    program.runBlock (dialect code) ⟨.l114300, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
