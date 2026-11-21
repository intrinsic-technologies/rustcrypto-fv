import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l1145af [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11255f bytes_l1145af) (entryMap (live .l1145af))
      7 0x11255f bytes_l1145af b_l1145af := by
  have f0 : InstrSpec 0x11255f [0x48, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x11255f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11255f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11255f 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11255f 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11255f 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x112564 [0x0F, 0xB6, 0x44, 0x24, 0x28] (LoadPre 0x112564 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112564 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x112564 5 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x112564 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_effect_step 0x112564 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x112569 [0x88, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x112569 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x112569 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x112569 7 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x112569 7 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m8_r8_effect_step 0x112569 0 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x112570 [0x0F, 0xB6, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x112570 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x112570 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x112570 8 0 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x112570 8 0 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (movzx_r32_m8_effect_step 0x112570 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x112578 [0x0F, 0xB6, 0x4C, 0x24, 0x50] (LoadPre 0x112578 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x112578 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x112578 5 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x112578 5 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (movzx_r32_m8_effect_step 0x112578 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11257d [0x88, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (StorePre 0x11257d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x11257d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x11257d 7 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11257d 7 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_m8_r8_effect_step 0x11257d 1 (by decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (4, 4), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x112564) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (2, 2), (4, 4), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x112569) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (2, 2), (4, 4), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x112570) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (2, 2), (4, 4), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x112578) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 58), (1, 60), (2, 2), (4, 4), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x11257d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 58), (1, 60), (2, 2), (4, 4), (6, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 19), (22, 22), (39, 39), (51, 51)]) (p' := 0x112584) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.jcc (n := 63) (jcc_rel32_effect_step 0x112584 4 0xfffffd26) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1145af [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1145af :=
  Rest.liftedBlock (rest_l1145af code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1145af x hx)

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

theorem_by block_l1145af_eval :
    program.runBlock (dialect code) ⟨.l1145af, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
