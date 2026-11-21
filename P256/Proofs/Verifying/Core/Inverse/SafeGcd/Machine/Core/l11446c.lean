import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l11446c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11241c bytes_l11446c) (entryMap (live .l11446c))
      15 0x11241c bytes_l11446c b_l11446c := by
  have f0 : InstrSpec 0x11241c [0x48, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x11241c) (addR64Imm8Effect 0x11241c 4 0x10)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11241c 4 0x10).toInstrSpec (add_r64_imm8_effect_step 0x11241c 0x48 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x112420 [0x48, 0x8B, 0x84, 0x24, 0x48, 0x01, 0x00, 0x00] (LoadPre 0x112420 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x112420 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112420 0 (.sib 4 none 0 (.d32 0x148)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112420 0 (.sib 4 none 0 (.d32 0x148))).toInstrSpec (mov_r64_m64_effect_step 0x112420 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x148)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x112428 [0x88, 0x44, 0x24, 0x07] (StorePre 0x112428 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x112428 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x112428 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x112428 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x112428 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x11242c [0x48, 0x8D, 0x4C, 0x24, 0x07] (fun s => s.RIP = 0x11242c) (leaR64Effect 0x11242c 1 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x11242c 1 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x11242c 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x112431 [0x48, 0x8B, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00] (LoadPre 0x112431 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x112431 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112431 0 (.sib 4 none 0 (.d32 0x130)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112431 0 (.sib 4 none 0 (.d32 0x130))).toInstrSpec (mov_r64_m64_effect_step 0x112431 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x130)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x112439 [0x88, 0x44, 0x24, 0x07] (StorePre 0x112439 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x112439 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x112439 4 0 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x112439 4 0 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_effect_step 0x112439 0 (by decide) (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x11243d [0x48, 0x8D, 0xBC, 0x24, 0xD8, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11243d) (leaR64Effect 0x11243d 7 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (leaR64Effect_footprint 0x11243d 7 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (lea_r64_effect_step 0x11243d 0x48 (by decide) 7 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112445 [0x48, 0x8D, 0x74, 0x24, 0x60] (fun s => s.RIP = 0x112445) (leaR64Effect 0x112445 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x112445 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x112445 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11244a [0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11244a) (leaR64Effect 0x11244a 2 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x11244a 2 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (lea_r64_effect_step 0x11244a 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x112452 [0x4C, 0x89, 0xE9] (fun s => s.RIP = 0x112452) (movR64R64Effect 0x112452 1 13)
      [.gpr 13] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x112452 1 13).toInstrSpec (mov_r64_r64_effect_step 0x112452 0x4c 0xe9 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x112455 [0x4D, 0x89, 0xF0] (fun s => s.RIP = 0x112455) (movR64R64Effect 0x112455 8 14)
      [.gpr 14] [] [.reg 8, .rip] :=
    (movR64R64Effect_footprint 0x112455 8 14).toInstrSpec (mov_r64_r64_effect_step 0x112455 0x4d 0xf0 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x112458 [0x41, 0x89, 0xE9] (fun s => s.RIP = 0x112458) (movR32R32Effect 0x112458 3 9 5)
      [.gpr 5] [] [.reg 9, .rip] :=
    (movR32R32Effect_footprint 0x112458 3 9 5).toInstrSpec (mov_r32_r32_rex_effect_step 0x112458 0x41 0xe9 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11245b [0x41, 0x57] (PushPre 0x11245b 2) (pushR64Effect 0x11245b 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11245b 2 15).toInstrSpec (push_r64_rex_effect_step 0x11245b 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f13 : InstrSpec 0x11245d [0x53] (PushPre 0x11245d 1) (pushR64Effect 0x11245d 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x11245d 1 3).toInstrSpec (push_r64_effect_step 0x11245d 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f14 : InstrSpec 0x11245e [0xE8, 0x5D, 0xF2, 0xFF, 0xFF] (PushPre 0x11245e 5) (callEffect (fun _ => 0x1116c0) 0x112463)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x11245e 0x1116c0 0x112463).toInstrSpec (call_rel32_effect_step 0x11245e 0xfffff25d (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112420) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112428) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11242c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112431) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112439) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11243d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112445) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11244a) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 59), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112452) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112455) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (8, 70), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112458) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 53), (5, 5), (6, 64), (7, 62), (8, 70), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11245b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 74), (5, 5), (6, 64), (7, 62), (8, 70), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11245d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 76), (5, 5), (6, 64), (7, 62), (8, 70), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11245e) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 59), (1, 68), (2, 66), (3, 3), (4, 78), (5, 5), (6, 64), (7, 62), (8, 70), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x1116c0) f14 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 80) (by decide) (by decide) rfl rfl

theorem block_l11446c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11446c :=
  Rest.liftedBlock (rest_l11446c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11446c x hx)

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

theorem_by block_l11446c_eval :
    program.runBlock (dialect code) ⟨.l11446c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
