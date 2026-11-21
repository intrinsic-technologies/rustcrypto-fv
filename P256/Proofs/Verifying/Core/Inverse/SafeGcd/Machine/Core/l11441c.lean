import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11441c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1123cc bytes_l11441c) (entryMap (live .l11441c))
      16 0x1123cc bytes_l11441c b_l11441c := by
  have f0 : InstrSpec 0x1123cc [0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00] (LoadPre 0x1123cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1123cc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1123cc 0 (.sib 4 none 0 (.d32 0x138)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x1123cc 0 (.sib 4 none 0 (.d32 0x138))).toInstrSpec (mov_r64_m64_effect_step 0x1123cc 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x138)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1123d4 [0x88, 0x44, 0x24, 0x07] (StorePre 0x1123d4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1123d4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1123d4 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1123d4 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1123d4 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1123d8 [0x48, 0x8D, 0x44, 0x24, 0x07] (fun s => s.RIP = 0x1123d8) (leaR64Effect 0x1123d8 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x1123d8 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x1123d8 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1123dd [0x48, 0x8B, 0x8C, 0x24, 0x40, 0x01, 0x00, 0x00] (LoadPre 0x1123dd (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1123dd + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1123dd 1 (.sib 4 none 0 (.d32 0x140)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1123dd 1 (.sib 4 none 0 (.d32 0x140))).toInstrSpec (mov_r64_m64_effect_step 0x1123dd 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x140)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1123e5 [0x88, 0x4C, 0x24, 0x07] (StorePre 0x1123e5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1123e5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1123e5 4 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x1123e5 4 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x1123e5 1 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1123e9 [0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1123e9) (leaR64Effect 0x1123e9 7 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x1123e9 7 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (lea_r64_effect_step 0x1123e9 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1123f1 [0x48, 0x8D, 0x74, 0x24, 0x60] (fun s => s.RIP = 0x1123f1) (leaR64Effect 0x1123f1 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x1123f1 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x1123f1 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1123f6 [0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1123f6) (leaR64Effect 0x1123f6 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1123f6 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x1123f6 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1123fe [0x48, 0x89, 0xD9] (fun s => s.RIP = 0x1123fe) (movR64R64Effect 0x1123fe 1 3)
      [.gpr 3] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x1123fe 1 3).toInstrSpec (mov_r64_r64_effect_step 0x1123fe 0x48 0xd9 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112401 [0x4D, 0x89, 0xF8] (fun s => s.RIP = 0x112401) (movR64R64Effect 0x112401 8 15)
      [.gpr 15] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x112401 8 15).toInstrSpec (mov_r64_r64_effect_step 0x112401 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112404 [0x41, 0x89, 0xE9] (fun s => s.RIP = 0x112404) (movR32R32Effect 0x112404 3 9 5)
      [.gpr 5] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x112404 3 9 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x112404 0x41 0xe9 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112407 [0x4C, 0x8B, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00] (LoadPre 0x112407 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x112407 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112407 15 (.sib 4 none 0 (.d32 0x128)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x112407 15 (.sib 4 none 0 (.d32 0x128))).toInstrSpec (mov_r64_m64_effect_step 0x112407 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0x128)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x11240f [0x41, 0x57] (PushPre 0x11240f 2) (pushR64Effect 0x11240f 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11240f 2 15).toInstrSpec (push_r64_rex_effect_step 0x11240f 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x112411 [0x48, 0x8B, 0x5C, 0x24, 0x60] (LoadPre 0x112411 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x112411 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112411 3 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x112411 3 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x112411 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x112416 [0x53] (PushPre 0x112416 1) (pushR64Effect 0x112416 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x112416 1 3).toInstrSpec (push_r64_effect_step 0x112416 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f15 : InstrSpec 0x112417 [0xE8, 0xA4, 0xF2, 0xFF, 0xFF] (PushPre 0x112417 5) (callEffect (fun _ => 0x1116c0) 0x11241c)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x112417 0x1116c0 0x11241c).toInstrSpec (call_rel32_effect_step 0x112417 0xfffff2a4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1123d4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1123d8) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1123dd) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 58), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1123e5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 56), (1, 58), (3, 3), (4, 4), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1123e9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 56), (1, 58), (3, 3), (4, 4), (5, 5), (7, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1123f1) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 56), (1, 58), (3, 3), (4, 4), (5, 5), (6, 63), (7, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1123f6) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 56), (1, 58), (2, 65), (3, 3), (4, 4), (5, 5), (6, 63), (7, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1123fe) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 56), (1, 67), (2, 65), (3, 3), (4, 4), (5, 5), (6, 63), (7, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112401) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 56), (1, 67), (2, 65), (3, 3), (4, 4), (5, 5), (6, 63), (7, 61), (8, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112404) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 56), (1, 67), (2, 65), (3, 3), (4, 4), (5, 5), (6, 63), (7, 61), (8, 69), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112407) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 56), (1, 67), (2, 65), (3, 3), (4, 4), (5, 5), (6, 63), (7, 61), (8, 69), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 73), (22, 22), (39, 39), (51, 51)]) (p' := 0x11240f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 56), (1, 67), (2, 65), (3, 3), (4, 75), (5, 5), (6, 63), (7, 61), (8, 69), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 73), (22, 22), (39, 39), (51, 51)]) (p' := 0x112411) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 56), (1, 67), (2, 65), (3, 77), (4, 75), (5, 5), (6, 63), (7, 61), (8, 69), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 73), (22, 22), (39, 39), (51, 51)]) (p' := 0x112416) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 56), (1, 67), (2, 65), (3, 77), (4, 79), (5, 5), (6, 63), (7, 61), (8, 69), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 73), (22, 22), (39, 39), (51, 51)]) (p' := 0x112417) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 56), (1, 67), (2, 65), (3, 77), (4, 81), (5, 5), (6, 63), (7, 61), (8, 69), (9, 71), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 73), (22, 22), (39, 39), (51, 51)]) (p' := 0x1116c0) f15 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 83) (by decide) (by decide) rfl rfl

theorem block_l11441c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11441c :=
  Rest.liftedBlock (rest_l11441c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11441c x hx)

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

theorem_by block_l11441c_eval :
    program.runBlock (dialect code) ⟨.l11441c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
