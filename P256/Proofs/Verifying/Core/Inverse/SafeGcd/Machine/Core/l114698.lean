import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l114698 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112648 bytes_l114698) (entryMap (live .l114698))
      11 0x112648 bytes_l114698 b_l114698 := by
  have f0 : InstrSpec 0x112648 [0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00] (LoadPre 0x112648 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x112648 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112648 0 (.sib 4 none 0 (.d32 0x118)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112648 0 (.sib 4 none 0 (.d32 0x118))).toInstrSpec (mov_r64_m64_effect_step 0x112648 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x118)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x112650 [0x48, 0x0B, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00] (LoadPre 0x112650 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x112650 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x112650 0 (.sib 4 none 0 (.d32 0x108)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x112650 0 (.sib 4 none 0 (.d32 0x108))).toInstrSpec (or_r64_m64_effect_step 0x112650 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x108)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x112658 [0x48, 0x0B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00] (LoadPre 0x112658 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x112658 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x112658 0 (.sib 4 none 0 (.d32 0x100)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x112658 0 (.sib 4 none 0 (.d32 0x100))).toInstrSpec (or_r64_m64_effect_step 0x112658 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x100)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x112660 [0x48, 0x0B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00] (LoadPre 0x112660 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x112660 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x112660 0 (.sib 4 none 0 (.d32 0x110)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (orR64M64Effect_footprint 0x112660 0 (.sib 4 none 0 (.d32 0x110))).toInstrSpec (or_r64_m64_effect_step 0x112660 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x110)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112668 [0x0F, 0x95, 0xC3] (fun s => s.RIP = 0x112668) (atFlags (condHolds 5) (setccR8Effect 0x112668 3 3))
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF] [.reg 3, .rip] :=
    (setccR8Effect_footprint 0x112668 3 3 5).toInstrSpec (StepEffect.atFlags fun c => (setcc_r8_effect_step 0x112668 5 0xc3 (by decide) (by decide) c)) pre_rip
  have f5 : InstrSpec 0x11266b [0x8B, 0x54, 0x24, 0x28] (LoadPre 0x11266b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11266b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x11266b 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x11266b 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r32_m32_low_effect_step 0x11266b 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11266f [0x48, 0x8D, 0x74, 0x24, 0x60] (fun s => s.RIP = 0x11266f) (leaR64Effect 0x11266f 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x11266f 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (lea_r64_effect_step 0x11266f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x112674 [0x4C, 0x8B, 0xB4, 0x24, 0x20, 0x01, 0x00, 0x00] (LoadPre 0x112674 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x112674 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x112674 14 (.sib 4 none 0 (.d32 0x120)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x112674 14 (.sib 4 none 0 (.d32 0x120))).toInstrSpec (mov_r64_m64_effect_step 0x112674 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0x120)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11267c [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x11267c) (movR64R64Effect 0x11267c 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11267c 7 14).toInstrSpec (mov_r64_r64_effect_step 0x11267c 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11267f [0x48, 0x8B, 0x4C, 0x24, 0x58] (LoadPre 0x11267f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x11267f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11267f 1 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11267f 1 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x11267f 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x112684 [0xE8, 0x37, 0x00, 0x00, 0x00] (PushPre 0x112684 5) (callEffect (fun _ => 0x1126c0) 0x112689)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x112684 0x1126c0 0x112689).toInstrSpec (call_rel32_effect_step 0x112684 0x37 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112650) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112658) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 57), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112660) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x112668) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 59), (3, 62), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x11266b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f5 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 59), (2, 64), (3, 62), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x11266f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 59), (2, 64), (3, 62), (4, 4), (5, 5), (6, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x112674) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f7 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 59), (2, 64), (3, 62), (4, 4), (5, 5), (6, 66), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (19, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x11267c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 59), (2, 64), (3, 62), (4, 4), (5, 5), (6, 66), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (19, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x11267f) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 59), (1, 72), (2, 64), (3, 62), (4, 4), (5, 5), (6, 66), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (19, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x112684) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 59), (1, 72), (2, 64), (3, 62), (4, 74), (5, 5), (6, 66), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 15), (19, 60), (22, 22), (39, 39), (51, 51)]) (p' := 0x1126c0) f10 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 76) (by decide) (by decide) rfl rfl

theorem block_l114698 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l114698 :=
  Rest.liftedBlock (rest_l114698 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l114698 x hx)

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

theorem_by block_l114698_eval :
    program.runBlock (dialect code) ⟨.l114698, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
