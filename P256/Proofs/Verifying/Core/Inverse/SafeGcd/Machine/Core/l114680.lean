import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l114680 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112630 bytes_l114680) (entryMap (live .l114680))
      4 0x112630 bytes_l114680 b_l114680 := by
  have f0 : InstrSpec 0x112630 [0x48, 0x01, 0xC1] (fun s => s.RIP = 0x112630) (addR64R64Effect 0x112630 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112630 1 0).toInstrSpec (add_r64_r64_effect_step 0x112630 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x112633 [0x49, 0x83, 0xC4, 0x02] (fun s => s.RIP = 0x112633) (addR64Imm8Effect 0x112633 12 0x2)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x112633 12 0x2).toInstrSpec (add_r64_imm8_effect_step 0x112633 0x49 0xc4 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x112637 [0x48, 0x01, 0xDE] (fun s => s.RIP = 0x112637) (addR64R64Effect 0x112637 6 3)
      [.gpr 6, .gpr 3] [] [.reg 6, .flags, .rip] :=
    (addR64R64Effect_footprint 0x112637 6 3).toInstrSpec (add_r64_r64_effect_step 0x112637 0x48 0xde (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11263a [0x4C, 0x01, 0xFF] (fun s => s.RIP = 0x11263a) (addR64R64Effect 0x11263a 7 15)
      [.gpr 7, .gpr 15] [] [.reg 7, .flags, .rip] :=
    (addR64R64Effect_footprint 0x11263a 7 15).toInstrSpec (add_r64_r64_effect_step 0x11263a 0x4c 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112633) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112637) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 7), (9, 9), (10, 10), (11, 11), (12, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11263a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 59), (9, 9), (10, 10), (11, 11), (12, 55), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11263d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 61) (by decide) rfl

theorem block_l114680 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l114680 :=
  Rest.liftedBlock (rest_l114680 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l114680 x hx)

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

theorem_by block_l114680_eval :
    program.runBlock (dialect code) ⟨.l114680, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
