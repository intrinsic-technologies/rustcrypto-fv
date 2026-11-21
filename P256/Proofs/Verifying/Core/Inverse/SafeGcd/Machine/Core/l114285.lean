import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Program
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Lift.Generated.Values

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

theorem rest_l114285 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x112235 bytes_l114285) (entryMap (live .l114285))
      14 0x112235 bytes_l114285 b_l114285 := by
  have f0 : InstrSpec 0x112235 [0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (StorePre 0x112235 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x112235 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x112235 (.sib 4 none 0 (.d32 0x80)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x112235 (.sib 4 none 0 (.d32 0x80)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x112235 0x48 (by decide) (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x112241 [0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00] (StorePre 0x112241 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x112241 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x112241 (.sib 4 none 0 (.d8 0x78)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x112241 (.sib 4 none 0 (.d8 0x78)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x112241 0x48 (by decide) (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11224a [0x48, 0xC7, 0x44, 0x24, 0x70, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11224a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x11224a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11224a (.sib 4 none 0 (.d8 0x70)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11224a (.sib 4 none 0 (.d8 0x70)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11224a 0x48 (by decide) (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x112253 [0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00] (StorePre 0x112253 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x112253 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x112253 (.sib 4 none 0 (.d8 0x68)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x112253 (.sib 4 none 0 (.d8 0x68)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x112253 0x48 (by decide) (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x11225c [0x48, 0xC7, 0x44, 0x24, 0x60, 0x00, 0x00, 0x00, 0x00] (StorePre 0x11225c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x11225c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11225c (.sib 4 none 0 (.d8 0x60)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x11225c (.sib 4 none 0 (.d8 0x60)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x11225c 0x48 (by decide) (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x112265 [0x49, 0x8B, 0x40, 0x18] (LoadPre 0x112265 (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x112265 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112265 0 (.base 8 (.d8 0x18)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112265 0 (.base 8 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x112265 0x49 (by decide) 0 (.base 8 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x112269 [0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112269 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x112269 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112269 0 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112269 0 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112269 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f7 : InstrSpec 0x112271 [0x49, 0x8B, 0x40, 0x10] (LoadPre 0x112271 (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x112271 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112271 0 (.base 8 (.d8 0x10)))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x112271 0 (.base 8 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x112271 0x49 (by decide) 0 (.base 8 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x112275 [0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112275 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x112275 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112275 0 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112275 0 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112275 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f9 : InstrSpec 0x11227d [0x49, 0x8B, 0x00] (LoadPre 0x11227d (fun s => AddrMode.addr (.base 8 .none) s (0x11227d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11227d 0 (.base 8 .none))
      [.gpr 8] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x11227d 0 (.base 8 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11227d 0x49 (by decide) 0 (.base 8 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x112280 [0x49, 0x8B, 0x48, 0x08] (LoadPre 0x112280 (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x112280 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112280 1 (.base 8 (.d8 0x8)))
      [.gpr 8] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x112280 1 (.base 8 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x112280 0x49 (by decide) 1 (.base 8 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x112284 [0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112284 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x112284 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x112284 1 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x112284 1 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x112284 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f12 : InstrSpec 0x11228c [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00] (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11228c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x11228c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x11228c 0 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x11228c 0 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.mov_m64_r64_effect_step_any 0x11228c 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre.of_addr rfl)
  have f13 : InstrSpec 0x112294 [0xC6, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00] (StorePre 0x112294 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x112294 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x112294 (.sib 4 none 0 (.d32 0xa8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x112294 (.sib 4 none 0 (.d32 0xa8)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x112294 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112241) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11224a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112253) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11225c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112265) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112269) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112271) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112275) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11227d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112280) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112284) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11228c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x112294) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 64), (1, 66), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (51, 51)]) (p' := 0x11229c) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 71) (by decide) rfl

theorem block_l114285 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l114285 :=
  Rest.liftedBlock (rest_l114285 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l114285 x hx)

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

theorem_by block_l114285_eval :
    program.runBlock (dialect code) ⟨.l114285, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
