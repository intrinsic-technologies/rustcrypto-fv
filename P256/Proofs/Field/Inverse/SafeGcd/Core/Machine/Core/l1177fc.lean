import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1177fc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111d1c bytes_l1177fc) (entryMap (live .l1177fc))
      16 0x111d1c bytes_l1177fc b_l1177fc := by
  have f0 : InstrSpec 0x111d1c [0x4C, 0x89, 0xF0] (fun s => s.RIP = 0x111d1c) (movR64R64Effect 0x111d1c 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x111d1c 0 14).toInstrSpec (mov_r64_r64_effect_step 0x111d1c 0x4c 0xf0 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111d1f [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x111d1f) (shrR64Effect 0x111d1f 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x111d1f 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x111d1f 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x111d23 [0x48, 0x89, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111d23 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x111d23 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111d23 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111d23 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111d23 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f3 : InstrSpec 0x111d2b [0x88, 0x44, 0x24, 0x03] (StorePre 0x111d2b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111d2b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111d2b 4 0 (.sib 4 none 0 (.d8 0x3)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111d2b 4 0 (.sib 4 none 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_effect_step 0x111d2b 0 (by decide) (.sib 4 none 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x111d2f [0x48, 0x8D, 0x4C, 0x24, 0x03] (fun s => s.RIP = 0x111d2f) (leaR64Effect 0x111d2f 1 (.sib 4 none 0 (.d8 0x3)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x111d2f 1 (.sib 4 none 0 (.d8 0x3))).toInstrSpec (lea_r64_effect_step 0x111d2f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x3)) (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x111d34 [0x4C, 0x89, 0xE0] (fun s => s.RIP = 0x111d34) (movR64R64Effect 0x111d34 0 12)
      [.gpr 12] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x111d34 0 12).toInstrSpec (mov_r64_r64_effect_step 0x111d34 0x4c 0xe0 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x111d37 [0x48, 0xC1, 0xE8, 0x3F] (fun s => s.RIP = 0x111d37) (shrR64Effect 0x111d37 4 0 63)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (shrR64Effect_footprint 0x111d37 4 0 63).toInstrSpec (shr_r64_imm8_effect_step 0x111d37 0x48 0xe8 0x3f (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111d3b [0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111d3b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x111d3b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x111d3b 0 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x111d3b 0 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x111d3b 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f8 : InstrSpec 0x111d43 [0x88, 0x44, 0x24, 0x03] (StorePre 0x111d43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111d43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111d43 4 0 (.sib 4 none 0 (.d8 0x3)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111d43 4 0 (.sib 4 none 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_effect_step 0x111d43 0 (by decide) (.sib 4 none 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x111d47 [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x111d47) (leaR64Effect 0x111d47 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x111d47 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x111d47 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111d4c [0x48, 0x8D, 0x74, 0x24, 0x58] (fun s => s.RIP = 0x111d4c) (leaR64Effect 0x111d4c 6 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x111d4c 6 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (lea_r64_effect_step 0x111d4c 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111d51 [0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111d51) (leaR64Effect 0x111d51 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x111d51 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x111d51 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x111d59 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x111d59) (movR64R64Effect 0x111d59 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x111d59 1 14).toInstrSpec (mov_r64_r64_effect_step 0x111d59 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111d5c [0x4D, 0x89, 0xE0] (fun s => s.RIP = 0x111d5c) (movR64R64Effect 0x111d5c 8 12)
      [.gpr 12] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x111d5c 8 12).toInstrSpec (mov_r64_r64_effect_step 0x111d5c 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x111d5f [0x44, 0x8B, 0x4C, 0x24, 0x04] (LoadPre 0x111d5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x111d5f + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x111d5f 9 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x111d5f 9 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x111d5f 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x111d64 [0xE8, 0x67, 0xF8, 0xFF, 0xFF] (PushPre 0x111d64 5) (callEffect (fun _ => 0x1115d0) 0x111d69)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x111d64 0x1115d0 0x111d69).toInstrSpec (call_rel32_effect_step 0x111d64 0xfffff867 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d1f) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d23) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d2b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d2f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d34) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 60), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d37) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d3b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d43) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d47) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d4c) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d51) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 62), (2, 70), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d59) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 62), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d5c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 62), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (8, 74), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d5f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 62), (1, 72), (2, 70), (3, 3), (4, 4), (5, 5), (6, 68), (7, 66), (8, 74), (9, 76), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111d64) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 62), (1, 72), (2, 70), (3, 3), (4, 78), (5, 5), (6, 68), (7, 66), (8, 74), (9, 76), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1115d0) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l1177fc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1177fc :=
  Rest.liftedBlock (rest_l1177fc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1177fc x hx)

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

theorem_by block_l1177fc_eval :
    program.runBlock (dialect code) ⟨.l1177fc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
