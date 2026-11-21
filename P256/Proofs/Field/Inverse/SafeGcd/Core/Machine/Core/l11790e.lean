import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11790e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x111e2e bytes_l11790e) (entryMap (live .l11790e))
      16 0x111e2e bytes_l11790e b_l11790e := by
  have f0 : InstrSpec 0x111e2e [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x111e2e) (addR64Imm8Effect 0x111e2e 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x111e2e 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x111e2e 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x111e32 [0x48, 0x8B, 0x84, 0x24, 0x40, 0x01, 0x00, 0x00] (LoadPre 0x111e32 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x111e32 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111e32 0 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111e32 0 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_r64_m64_effect_step 0x111e32 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x111e3a [0x88, 0x44, 0x24, 0x03] (StorePre 0x111e3a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111e3a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111e3a 4 0 (.sib 4 none 0 (.d8 0x3)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111e3a 4 0 (.sib 4 none 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_effect_step 0x111e3a 0 (by decide) (.sib 4 none 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x111e3e [0x48, 0x8D, 0x4C, 0x24, 0x03] (fun s => s.RIP = 0x111e3e) (leaR64Effect 0x111e3e 1 (.sib 4 none 0 (.d8 0x3)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x111e3e 1 (.sib 4 none 0 (.d8 0x3))).toInstrSpec (lea_r64_effect_step 0x111e3e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x3)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x111e43 [0x48, 0x8B, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x111e43 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x111e43 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x111e43 0 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x111e43 0 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_r64_m64_effect_step 0x111e43 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x111e4b [0x88, 0x44, 0x24, 0x03] (StorePre 0x111e4b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x111e4b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x111e4b 4 0 (.sib 4 none 0 (.d8 0x3)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x111e4b 4 0 (.sib 4 none 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_effect_step 0x111e4b 0 (by decide) (.sib 4 none 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x111e4f [0x48, 0x8D, 0x7C, 0x24, 0x30] (fun s => s.RIP = 0x111e4f) (leaR64Effect 0x111e4f 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x111e4f 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (lea_r64_effect_step 0x111e4f 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x111e54 [0x48, 0x8D, 0xB4, 0x24, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111e54) (leaR64Effect 0x111e54 6 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x111e54 6 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (lea_r64_effect_step 0x111e54 0x48 (by decide) 6 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x111e5c [0x48, 0x8D, 0x94, 0x24, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x111e5c) (leaR64Effect 0x111e5c 2 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x111e5c 2 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (lea_r64_effect_step 0x111e5c 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x111e64 [0x4C, 0x89, 0xF1] (fun s => s.RIP = 0x111e64) (movR64R64Effect 0x111e64 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x111e64 1 14).toInstrSpec (mov_r64_r64_effect_step 0x111e64 0x4c 0xf1 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x111e67 [0x4D, 0x89, 0xE0] (fun s => s.RIP = 0x111e67) (movR64R64Effect 0x111e67 8 12)
      [.gpr 12] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x111e67 8 12).toInstrSpec (mov_r64_r64_effect_step 0x111e67 0x4d 0xe0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x111e6a [0x44, 0x8B, 0x74, 0x24, 0x04] (LoadPre 0x111e6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x111e6a + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x111e6a 14 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x111e6a 14 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x111e6a 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x111e6f [0x45, 0x89, 0xF1] (fun s => s.RIP = 0x111e6f) (movR32R32Effect 0x111e6f 3 9 14)
      [.gpr 14] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x111e6f 3 9 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x111e6f 0x45 0xf1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x111e72 [0x41, 0x57] (PushPre 0x111e72 2) (pushR64Effect 0x111e72 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x111e72 2 15).toInstrSpec (push_r64_rex_effect_step 0x111e72 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x111e74 [0x53] (PushPre 0x111e74 1) (pushR64Effect 0x111e74 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x111e74 1 3).toInstrSpec (push_r64_effect_step 0x111e74 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x111e75 [0xE8, 0x46, 0xF8, 0xFF, 0xFF] (PushPre 0x111e75 5) (callEffect (fun _ => 0x1116c0) 0x111e7a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x111e75 0x1116c0 0x111e7a).toInstrSpec (call_rel32_effect_step 0x111e75 0xfffff846 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e32) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e3a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e3e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e43) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e4b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e4f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e54) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e5c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 59), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e64) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e67) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (8, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e6a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (8, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 72), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e6f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (8, 70), (9, 74), (10, 10), (11, 11), (12, 12), (13, 13), (14, 72), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e72) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 76), (5, 5), (6, 64), (7, 62), (8, 70), (9, 74), (10, 10), (11, 11), (12, 12), (13, 13), (14, 72), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e74) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 78), (5, 5), (6, 64), (7, 62), (8, 70), (9, 74), (10, 10), (11, 11), (12, 12), (13, 13), (14, 72), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x111e75) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 80), (5, 5), (6, 64), (7, 62), (8, 70), (9, 74), (10, 10), (11, 11), (12, 12), (13, 13), (14, 72), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1116c0) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 82) (by decide) (by decide) rfl rfl

theorem block_l11790e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11790e :=
  Rest.liftedBlock (rest_l11790e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11790e x hx)

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

theorem_by block_l11790e_eval :
    program.runBlock (dialect code) ⟨.l11790e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Field.Inverse.SafeGcd.Core.Machine
