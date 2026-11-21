import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l103f30 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f30 bytes_l103f30) (entryMap (live .l103f30))
      4 0x103f30 bytes_l103f30 b_l103f30 := by
  have f0 : InstrSpec 0x103f30 [0x50] (PushPre 0x103f30 1) (pushR64Effect 0x103f30 1 0)
      [.gpr 4, .gpr 0] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x103f30 1 0).toInstrSpec (push_r64_effect_step 0x103f30 0x50 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x103f31 [0x48, 0x8D, 0x42, 0x07] (fun s => s.RIP = 0x103f31) (leaR64Effect 0x103f31 0 (.base 2 (.d8 0x7)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103f31 0 (.base 2 (.d8 0x7))).toInstrSpec (lea_r64_effect_step 0x103f31 0x48 (by decide) 0 (.base 2 (.d8 0x7)) (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x103f35 [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x103f35) (cmpR64R64Effect 0x103f35 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103f35 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x103f35 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f31) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f35) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f38) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 59) (jcc_rel32_effect_step 0x103f38 3 0xbc) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103f30 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f30 :=
  Rest.liftedBlock (rest_l103f30 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f30 x hx)

theorem rest_l103f3e [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f3e bytes_l103f3e) (entryMap (live .l103f3e))
      3 0x103f3e bytes_l103f3e b_l103f3e := by
  have f0 : InstrSpec 0x103f3e [0x48, 0x8D, 0x42, 0x0F] (fun s => s.RIP = 0x103f3e) (leaR64Effect 0x103f3e 0 (.base 2 (.d8 0xf)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103f3e 0 (.base 2 (.d8 0xf))).toInstrSpec (lea_r64_effect_step 0x103f3e 0x48 (by decide) 0 (.base 2 (.d8 0xf)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103f42 [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x103f42) (cmpR64R64Effect 0x103f42 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103f42 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x103f42 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f42) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f45) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x103f45 3 0x9d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103f3e [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f3e :=
  Rest.liftedBlock (rest_l103f3e code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f3e x hx)

theorem rest_l103f4b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f4b bytes_l103f4b) (entryMap (live .l103f4b))
      5 0x103f4b bytes_l103f4b b_l103f4b := by
  have f0 : InstrSpec 0x103f4b [0x0F, 0xB7, 0x44, 0x57, 0x0E] (LoadPre 0x103f4b (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xe)) s (0x103f4b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103f4b 5 0 (.sib 7 (some 2) 1 (.d8 0xe)))
      [.gpr 7, .gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x103f4b 5 0 (.sib 7 (some 2) 1 (.d8 0xe))).toInstrSpec (movzx_r32_m16_effect_step 0x103f4b 0 (.sib 7 (some 2) 1 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103f50 [0x66, 0x89, 0x44, 0x57, 0x1E] (StorePre 0x103f50 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1e)) s (0x103f50 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103f50 5 0 (.sib 7 (some 2) 1 (.d8 0x1e)))
      [.gpr 0, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x103f50 5 0 (.sib 7 (some 2) 1 (.d8 0x1e))).toInstrSpec (mov_m16_r16_effect_step 0x103f50 0 (.sib 7 (some 2) 1 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103f55 [0x48, 0x8D, 0x42, 0x06] (fun s => s.RIP = 0x103f55) (leaR64Effect 0x103f55 0 (.base 2 (.d8 0x6)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103f55 0 (.base 2 (.d8 0x6))).toInstrSpec (lea_r64_effect_step 0x103f55 0x48 (by decide) 0 (.base 2 (.d8 0x6)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103f59 [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x103f59) (cmpR64R64Effect 0x103f59 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103f59 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x103f59 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f50) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f55) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f59) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f5c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel32_effect_step 0x103f5c 3 0x98) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103f4b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f4b :=
  Rest.liftedBlock (rest_l103f4b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f4b x hx)

theorem rest_l103f62 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f62 bytes_l103f62) (entryMap (live .l103f62))
      5 0x103f62 bytes_l103f62 b_l103f62 := by
  have f0 : InstrSpec 0x103f62 [0x0F, 0xB7, 0x44, 0x57, 0x0C] (LoadPre 0x103f62 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xc)) s (0x103f62 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103f62 5 0 (.sib 7 (some 2) 1 (.d8 0xc)))
      [.gpr 7, .gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x103f62 5 0 (.sib 7 (some 2) 1 (.d8 0xc))).toInstrSpec (movzx_r32_m16_effect_step 0x103f62 0 (.sib 7 (some 2) 1 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103f67 [0x66, 0x89, 0x44, 0x57, 0x1C] (StorePre 0x103f67 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1c)) s (0x103f67 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103f67 5 0 (.sib 7 (some 2) 1 (.d8 0x1c)))
      [.gpr 0, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x103f67 5 0 (.sib 7 (some 2) 1 (.d8 0x1c))).toInstrSpec (mov_m16_r16_effect_step 0x103f67 0 (.sib 7 (some 2) 1 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103f6c [0x48, 0x8D, 0x42, 0x05] (fun s => s.RIP = 0x103f6c) (leaR64Effect 0x103f6c 0 (.base 2 (.d8 0x5)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103f6c 0 (.base 2 (.d8 0x5))).toInstrSpec (lea_r64_effect_step 0x103f6c 0x48 (by decide) 0 (.base 2 (.d8 0x5)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103f70 [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x103f70) (cmpR64R64Effect 0x103f70 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103f70 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x103f70 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f67) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f6c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f70) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f73) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel32_effect_step 0x103f73 3 0x81) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103f62 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f62 :=
  Rest.liftedBlock (rest_l103f62 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f62 x hx)

theorem rest_l103f79 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f79 bytes_l103f79) (entryMap (live .l103f79))
      5 0x103f79 bytes_l103f79 b_l103f79 := by
  have f0 : InstrSpec 0x103f79 [0x0F, 0xB7, 0x44, 0x57, 0x0A] (LoadPre 0x103f79 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0xa)) s (0x103f79 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103f79 5 0 (.sib 7 (some 2) 1 (.d8 0xa)))
      [.gpr 7, .gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x103f79 5 0 (.sib 7 (some 2) 1 (.d8 0xa))).toInstrSpec (movzx_r32_m16_effect_step 0x103f79 0 (.sib 7 (some 2) 1 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103f7e [0x66, 0x89, 0x44, 0x57, 0x1A] (StorePre 0x103f7e 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1a)) s (0x103f7e + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103f7e 5 0 (.sib 7 (some 2) 1 (.d8 0x1a)))
      [.gpr 0, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x103f7e 5 0 (.sib 7 (some 2) 1 (.d8 0x1a))).toInstrSpec (mov_m16_r16_effect_step 0x103f7e 0 (.sib 7 (some 2) 1 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103f83 [0x48, 0x8D, 0x42, 0x04] (fun s => s.RIP = 0x103f83) (leaR64Effect 0x103f83 0 (.base 2 (.d8 0x4)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103f83 0 (.base 2 (.d8 0x4))).toInstrSpec (lea_r64_effect_step 0x103f83 0x48 (by decide) 0 (.base 2 (.d8 0x4)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103f87 [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x103f87) (cmpR64R64Effect 0x103f87 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103f87 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x103f87 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f7e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f83) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f87) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f8a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x103f8a 3 0x6e) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103f79 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f79 :=
  Rest.liftedBlock (rest_l103f79 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f79 x hx)

theorem rest_l103f8c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f8c bytes_l103f8c) (entryMap (live .l103f8c))
      5 0x103f8c bytes_l103f8c b_l103f8c := by
  have f0 : InstrSpec 0x103f8c [0x0F, 0xB7, 0x44, 0x57, 0x08] (LoadPre 0x103f8c (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x8)) s (0x103f8c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103f8c 5 0 (.sib 7 (some 2) 1 (.d8 0x8)))
      [.gpr 7, .gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x103f8c 5 0 (.sib 7 (some 2) 1 (.d8 0x8))).toInstrSpec (movzx_r32_m16_effect_step 0x103f8c 0 (.sib 7 (some 2) 1 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103f91 [0x66, 0x89, 0x44, 0x57, 0x18] (StorePre 0x103f91 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x18)) s (0x103f91 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103f91 5 0 (.sib 7 (some 2) 1 (.d8 0x18)))
      [.gpr 0, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x103f91 5 0 (.sib 7 (some 2) 1 (.d8 0x18))).toInstrSpec (mov_m16_r16_effect_step 0x103f91 0 (.sib 7 (some 2) 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103f96 [0x48, 0x8D, 0x42, 0x03] (fun s => s.RIP = 0x103f96) (leaR64Effect 0x103f96 0 (.base 2 (.d8 0x3)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103f96 0 (.base 2 (.d8 0x3))).toInstrSpec (lea_r64_effect_step 0x103f96 0x48 (by decide) 0 (.base 2 (.d8 0x3)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103f9a [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x103f9a) (cmpR64R64Effect 0x103f9a 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103f9a 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x103f9a 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f91) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f96) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f9a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103f9d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x103f9d 3 0x5b) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103f8c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f8c :=
  Rest.liftedBlock (rest_l103f8c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f8c x hx)

theorem rest_l103f9f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103f9f bytes_l103f9f) (entryMap (live .l103f9f))
      5 0x103f9f bytes_l103f9f b_l103f9f := by
  have f0 : InstrSpec 0x103f9f [0x0F, 0xB7, 0x44, 0x57, 0x06] (LoadPre 0x103f9f (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x6)) s (0x103f9f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103f9f 5 0 (.sib 7 (some 2) 1 (.d8 0x6)))
      [.gpr 7, .gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x103f9f 5 0 (.sib 7 (some 2) 1 (.d8 0x6))).toInstrSpec (movzx_r32_m16_effect_step 0x103f9f 0 (.sib 7 (some 2) 1 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103fa4 [0x66, 0x89, 0x44, 0x57, 0x16] (StorePre 0x103fa4 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x16)) s (0x103fa4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103fa4 5 0 (.sib 7 (some 2) 1 (.d8 0x16)))
      [.gpr 0, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x103fa4 5 0 (.sib 7 (some 2) 1 (.d8 0x16))).toInstrSpec (mov_m16_r16_effect_step 0x103fa4 0 (.sib 7 (some 2) 1 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103fa9 [0x48, 0x8D, 0x42, 0x02] (fun s => s.RIP = 0x103fa9) (leaR64Effect 0x103fa9 0 (.base 2 (.d8 0x2)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103fa9 0 (.base 2 (.d8 0x2))).toInstrSpec (lea_r64_effect_step 0x103fa9 0x48 (by decide) 0 (.base 2 (.d8 0x2)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103fad [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x103fad) (cmpR64R64Effect 0x103fad 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103fad 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x103fad 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fa4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fa9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fad) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fb0) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x103fb0 3 0x48) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103f9f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103f9f :=
  Rest.liftedBlock (rest_l103f9f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103f9f x hx)

theorem rest_l103fb2 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103fb2 bytes_l103fb2) (entryMap (live .l103fb2))
      5 0x103fb2 bytes_l103fb2 b_l103fb2 := by
  have f0 : InstrSpec 0x103fb2 [0x0F, 0xB7, 0x44, 0x57, 0x04] (LoadPre 0x103fb2 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x4)) s (0x103fb2 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103fb2 5 0 (.sib 7 (some 2) 1 (.d8 0x4)))
      [.gpr 7, .gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x103fb2 5 0 (.sib 7 (some 2) 1 (.d8 0x4))).toInstrSpec (movzx_r32_m16_effect_step 0x103fb2 0 (.sib 7 (some 2) 1 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103fb7 [0x66, 0x89, 0x44, 0x57, 0x14] (StorePre 0x103fb7 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x14)) s (0x103fb7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103fb7 5 0 (.sib 7 (some 2) 1 (.d8 0x14)))
      [.gpr 0, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x103fb7 5 0 (.sib 7 (some 2) 1 (.d8 0x14))).toInstrSpec (mov_m16_r16_effect_step 0x103fb7 0 (.sib 7 (some 2) 1 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103fbc [0x48, 0x8D, 0x42, 0x01] (fun s => s.RIP = 0x103fbc) (leaR64Effect 0x103fbc 0 (.base 2 (.d8 0x1)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103fbc 0 (.base 2 (.d8 0x1))).toInstrSpec (lea_r64_effect_step 0x103fbc 0x48 (by decide) 0 (.base 2 (.d8 0x1)) (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x103fc0 [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x103fc0) (cmpR64R64Effect 0x103fc0 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103fc0 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x103fc0 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fb7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fbc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fc0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fc3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 60) (jcc_rel8_effect_step 0x103fc3 3 0x35) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103fb2 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103fb2 :=
  Rest.liftedBlock (rest_l103fb2 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103fb2 x hx)

theorem rest_l103fc5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103fc5 bytes_l103fc5) (entryMap (live .l103fc5))
      4 0x103fc5 bytes_l103fc5 b_l103fc5 := by
  have f0 : InstrSpec 0x103fc5 [0x0F, 0xB7, 0x44, 0x57, 0x02] (LoadPre 0x103fc5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x2)) s (0x103fc5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x103fc5 5 0 (.sib 7 (some 2) 1 (.d8 0x2)))
      [.gpr 7, .gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x103fc5 5 0 (.sib 7 (some 2) 1 (.d8 0x2))).toInstrSpec (movzx_r32_m16_effect_step 0x103fc5 0 (.sib 7 (some 2) 1 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103fca [0x66, 0x89, 0x44, 0x57, 0x12] (StorePre 0x103fca 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x12)) s (0x103fca + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103fca 5 0 (.sib 7 (some 2) 1 (.d8 0x12)))
      [.gpr 0, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x103fca 5 0 (.sib 7 (some 2) 1 (.d8 0x12))).toInstrSpec (mov_m16_r16_effect_step 0x103fca 0 (.sib 7 (some 2) 1 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103fcf [0x48, 0x39, 0xF2] (fun s => s.RIP = 0x103fcf) (cmpR64R64Effect 0x103fcf 2 6)
      [.gpr 2, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103fcf 2 6).toInstrSpec (cmp_r64_r64_effect_step 0x103fcf 0x48 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fca) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fcf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fd2) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x103fd2 3 0x23) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103fc5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103fc5 :=
  Rest.liftedBlock (rest_l103fc5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103fc5 x hx)

theorem rest_l103fd4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103fd4 bytes_l103fd4) (entryMap (live .l103fd4))
      3 0x103fd4 bytes_l103fd4 b_l103fd4 := by
  have f0 : InstrSpec 0x103fd4 [0x48, 0x8D, 0x42, 0x08] (fun s => s.RIP = 0x103fd4) (leaR64Effect 0x103fd4 0 (.base 2 (.d8 0x8)))
      [.gpr 2] [] [.reg 0, .rip] :=
    (leaR64Effect_footprint 0x103fd4 0 (.base 2 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x103fd4 0x48 (by decide) 0 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103fd8 [0x48, 0x39, 0xF0] (fun s => s.RIP = 0x103fd8) (cmpR64R64Effect 0x103fd8 0 6)
      [.gpr 0, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x103fd8 0 6).toInstrSpec (cmp_r64_r64_effect_step 0x103fd8 0x48 0xf0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fd8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fdb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel8_effect_step 0x103fdb 3 0xb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l103fd4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103fd4 :=
  Rest.liftedBlock (rest_l103fd4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103fd4 x hx)

theorem rest_l103fdd [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103fdd bytes_l103fdd) (entryMap (live .l103fdd))
      4 0x103fdd bytes_l103fdd b_l103fdd := by
  have f0 : InstrSpec 0x103fdd [0x0F, 0xB7, 0x04, 0x57] (LoadPre 0x103fdd (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x103fdd + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x103fdd 4 0 (.sib 7 (some 2) 1 .none))
      [.gpr 7, .gpr 2] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x103fdd 4 0 (.sib 7 (some 2) 1 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x103fdd 0 (.sib 7 (some 2) 1 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x103fe1 [0x66, 0x89, 0x44, 0x57, 0x10] (StorePre 0x103fe1 5 (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x10)) s (0x103fe1 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x103fe1 5 0 (.sib 7 (some 2) 1 (.d8 0x10)))
      [.gpr 0, .gpr 7, .gpr 2] [] [.rip] :=
    (movM16R16Effect_footprint 0x103fe1 5 0 (.sib 7 (some 2) 1 (.d8 0x10))).toInstrSpec (mov_m16_r16_effect_step 0x103fe1 0 (.sib 7 (some 2) 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x103fe6 [0x58] (PopPre 0x103fe6) (popR64Effect 0x103fe6 1 0)
      [.gpr 4] [] [.reg 0, .reg 4, .rip] :=
    (popR64Effect_footprint 0x103fe6 1 0).toInstrSpec (pop_r64_effect_step 0x103fe6 0x58 (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x103fe7 [0xC3] (RetPre 0x103fe7) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x103fe7).toInstrSpec (ret_effect_step 0x103fe7) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fe1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fe6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 58) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x103fe7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 60) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 61) (ρ' := [(0, 56), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f3 (by decide) rfl rfl rfl (by decide)

theorem block_l103fdd [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103fdd :=
  Rest.liftedBlock (rest_l103fdd code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103fdd x hx)

theorem rest_l103fe8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103fe8 bytes_l103fe8) (entryMap (live .l103fe8))
      3 0x103fe8 bytes_l103fe8 b_l103fe8 := by
  have f0 : InstrSpec 0x103fe8 [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x103fe8) (movR64R64Effect 0x103fe8 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103fe8 7 0).toInstrSpec (mov_r64_r64_effect_step 0x103fe8 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103feb [0x48, 0xC7, 0xC2, 0x10, 0x10, 0x20, 0x00] (fun s => s.RIP = 0x103feb) (movR64Imm32Effect 0x103feb 2 0x201010)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x103feb 2 0x201010).toInstrSpec (mov_r64_imm32_effect_step 0x103feb 0x48 0xc2 (by decide) (by decide) (by decide) 0x201010) pre_rip
  have f2 : InstrSpec 0x103ff2 [0xE8, 0x40, 0xF8, 0xFF, 0xFF] (PushPre 0x103ff2 5) (callEffect (fun _ => 0x103837) 0x103ff7)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x103ff2 0x103837 0x103ff7).toInstrSpec (call_rel32_effect_step 0x103ff2 0xfffff840 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x103feb) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x103ff2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x103837) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l103fe8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103fe8 :=
  Rest.liftedBlock (rest_l103fe8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103fe8 x hx)

theorem rest_l103ff7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103ff7 bytes_l103ff7) (entryMap (live .l103ff7))
      1 0x103ff7 bytes_l103ff7 b_l103ff7 := by
  have f0 : InstrSpec 0x103ff7 [0x48, 0x89, 0xD0] (fun s => s.RIP = 0x103ff7) (movR64R64Effect 0x103ff7 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x103ff7 0 2).toInstrSpec (mov_r64_r64_effect_step 0x103ff7 0x48 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (2, 2), (4, 4), (5, 5), (6, 6)]) (p' := 0x103ffa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l103ff7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103ff7 :=
  Rest.liftedBlock (rest_l103ff7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103ff7 x hx)

theorem rest_l103ffa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x103ffa bytes_l103ffa) (entryMap (live .l103ffa))
      3 0x103ffa bytes_l103ffa b_l103ffa := by
  have f0 : InstrSpec 0x103ffa [0x48, 0x89, 0xC7] (fun s => s.RIP = 0x103ffa) (movR64R64Effect 0x103ffa 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x103ffa 7 0).toInstrSpec (mov_r64_r64_effect_step 0x103ffa 0x48 0xc7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x103ffd [0x48, 0xC7, 0xC2, 0xF8, 0x0F, 0x20, 0x00] (fun s => s.RIP = 0x103ffd) (movR64Imm32Effect 0x103ffd 2 0x200ff8)
      [] [] [.reg 2, .rip] :=
    (movR64Imm32Effect_footprint 0x103ffd 2 0x200ff8).toInstrSpec (mov_r64_imm32_effect_step 0x103ffd 0x48 0xc2 (by decide) (by decide) (by decide) 0x200ff8) pre_rip
  have f2 : InstrSpec 0x104004 [0xE8, 0x2E, 0xF8, 0xFF, 0xFF] (PushPre 0x104004 5) (callEffect (fun _ => 0x103837) 0x104009)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x104004 0x103837 0x104009).toInstrSpec (call_rel32_effect_step 0x104004 0xfffff82e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x103ffd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 55), (4, 4), (5, 5), (6, 6), (7, 53)]) (p' := 0x104004) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 55), (4, 57), (5, 5), (6, 6), (7, 53)]) (p' := 0x103837) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l103ffa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l103ffa :=
  Rest.liftedBlock (rest_l103ffa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l103ffa x hx)

theorem rest_l104009 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x104009 bytes_l104009) (entryMap (live .l104009))
      1 0x104009 bytes_l104009 b_l104009 := by
  have f0 : InstrSpec 0x104009 [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x104009) (fun _ => nopEffect 0x104009 7)
      [] [] [.rip] :=
    (nopEffect_footprint 0x104009 7).toInstrSpec (nop_m_effect_step 0x104009 [] (by decide) (by decide) (.base 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x104010) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l104009 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l104009 :=
  Rest.liftedBlock (rest_l104009 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l104009 x hx)

theorem rest_l109980 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109980 bytes_l109980) (entryMap (live .l109980))
      16 0x109980 bytes_l109980 b_l109980 := by
  have f0 : InstrSpec 0x109980 [0x55] (PushPre 0x109980 1) (pushR64Effect 0x109980 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109980 1 5).toInstrSpec (push_r64_effect_step 0x109980 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x109981 [0x41, 0x57] (PushPre 0x109981 2) (pushR64Effect 0x109981 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109981 2 15).toInstrSpec (push_r64_rex_effect_step 0x109981 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109983 [0x41, 0x56] (PushPre 0x109983 2) (pushR64Effect 0x109983 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109983 2 14).toInstrSpec (push_r64_rex_effect_step 0x109983 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109985 [0x41, 0x55] (PushPre 0x109985 2) (pushR64Effect 0x109985 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109985 2 13).toInstrSpec (push_r64_rex_effect_step 0x109985 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x109987 [0x41, 0x54] (PushPre 0x109987 2) (pushR64Effect 0x109987 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109987 2 12).toInstrSpec (push_r64_rex_effect_step 0x109987 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x109989 [0x53] (PushPre 0x109989 1) (pushR64Effect 0x109989 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x109989 1 3).toInstrSpec (push_r64_effect_step 0x109989 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10998a [0x48, 0x83, 0xEC, 0x28] (fun s => s.RIP = 0x10998a) (subR64Imm8Effect 0x10998a 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10998a 4 0x28).toInstrSpec (sub_r64_imm8_effect_step 0x10998a 0x48 0xec 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10998e [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x10998e) (movR64R64Effect 0x10998e 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10998e 3 6).toInstrSpec (mov_r64_r64_effect_step 0x10998e 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x109991 [0x49, 0x89, 0xFE] (fun s => s.RIP = 0x109991) (movR64R64Effect 0x109991 14 7)
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x109991 14 7).toInstrSpec (mov_r64_r64_effect_step 0x109991 0x49 0xfe (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x109994 [0x48, 0x89, 0x7C, 0x24, 0x20] (StorePre 0x109994 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109994 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109994 7 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109994 7 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x109994 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x109999 [0x48, 0x89, 0x54, 0x24, 0x18] (StorePre 0x109999 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109999 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109999 2 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109999 2 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109999 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10999e [0x49, 0x89, 0xD5] (fun s => s.RIP = 0x10999e) (movR64R64Effect 0x10999e 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR64R64Effect_footprint 0x10999e 13 2).toInstrSpec (mov_r64_r64_effect_step 0x10999e 0x49 0xd5 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1099a1 [0x49, 0xC1, 0xE5, 0x04] (fun s => s.RIP = 0x1099a1) (shlR64Effect 0x1099a1 4 13 4)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (shlR64Effect_footprint 0x1099a1 4 13 4).toInstrSpec (shl_r64_imm8_effect_step 0x1099a1 0x49 0xe5 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1099a5 [0x48, 0xBD, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F] (fun s => s.RIP = 0x1099a5) (movR64Imm64Effect 0x1099a5 5 0x7fffffffffffffc0)
      [] [] [.reg 5, .rip] :=
    (movR64Imm64Effect_footprint 0x1099a5 5 0x7fffffffffffffc0).toInstrSpec (mov_r64_imm64_effect_step 0x1099a5 0x48 0xbd (by decide) (by decide) 0x7fffffffffffffc0) pre_rip
  have f14 : InstrSpec 0x1099af [0x4C, 0x21, 0xED] (fun s => s.RIP = 0x1099af) (andR64R64Effect 0x1099af 5 13)
      [.gpr 5, .gpr 13] [] [.reg 5, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1099af 5 13).toInstrSpec (and_r64_r64_effect_step 0x1099af 0x4c 0xed (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109981) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109983) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109985) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109987) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109989) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10998a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10998e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109991) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109994) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109999) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10999e) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 73), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099a1) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 75), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099a5) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 65), (5, 77), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 75), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099af) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 80) f14 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 67), (4, 65), (5, 79), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 75), (14, 69), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099b2) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 82) (jcc_rel8_effect_step 0x1099b2 4 0x21) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109980 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109980 :=
  Rest.liftedBlock (rest_l109980 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109980 x hx)

theorem rest_l1099b4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1099b4 bytes_l1099b4) (entryMap (live .l1099b4))
      3 0x1099b4 bytes_l1099b4 b_l1099b4 := by
  have f0 : InstrSpec 0x1099b4 [0x4C, 0x8D, 0x64, 0x24, 0x20] (fun s => s.RIP = 0x1099b4) (leaR64Effect 0x1099b4 12 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (leaR64Effect_footprint 0x1099b4 12 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (lea_r64_effect_step 0x1099b4 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1099b9 [0x48, 0x89, 0xDE] (fun s => s.RIP = 0x1099b9) (movR64R64Effect 0x1099b9 6 3)
      [.gpr 3] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1099b9 6 3).toInstrSpec (mov_r64_r64_effect_step 0x1099b9 0x48 0xde (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1099bc [0x0F, 0x1F, 0x40, 0x00] (fun s => s.RIP = 0x1099bc) (fun _ => nopEffect 0x1099bc 4)
      [] [] [.rip] :=
    (nopEffect_footprint 0x1099bc 4).toInstrSpec (nop_m_effect_step 0x1099bc [] (by decide) (by decide) (.base 0 (.d8 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (12, 53), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099b9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (12, 53), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099bc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 55), (12, 53), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 58) (by decide) rfl

theorem block_l1099b4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1099b4 :=
  Rest.liftedBlock (rest_l1099b4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1099b4 x hx)

theorem rest_l1099c0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1099c0 bytes_l1099c0) (entryMap (live .l1099c0))
      3 0x1099c0 bytes_l1099c0 b_l1099c0 := by
  have f0 : InstrSpec 0x1099c0 [0x4C, 0x8D, 0x7E, 0x40] (fun s => s.RIP = 0x1099c0) (leaR64Effect 0x1099c0 15 (.base 6 (.d8 0x40)))
      [.gpr 6] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1099c0 15 (.base 6 (.d8 0x40))).toInstrSpec (lea_r64_effect_step 0x1099c0 0x4c (by decide) 7 (.base 6 (.d8 0x40)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1099c4 [0x4C, 0x89, 0xE7] (fun s => s.RIP = 0x1099c4) (movR64R64Effect 0x1099c4 7 12)
      [.gpr 12] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1099c4 7 12).toInstrSpec (mov_r64_r64_effect_step 0x1099c4 0x4c 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1099c7 [0xE8, 0xF4, 0x00, 0x00, 0x00] (PushPre 0x1099c7 5) (callEffect (fun _ => 0x109ac0) 0x1099cc)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1099c7 0x109ac0 0x1099cc).toInstrSpec (call_rel32_effect_step 0x1099c7 0xf4 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c4) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099c7) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ac0) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l1099c0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1099c0 :=
  Rest.liftedBlock (rest_l1099c0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1099c0 x hx)

theorem rest_l1099cc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1099cc bytes_l1099cc) (entryMap (live .l1099cc))
      3 0x1099cc bytes_l1099cc b_l1099cc := by
  have f0 : InstrSpec 0x1099cc [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x1099cc) (movR64R64Effect 0x1099cc 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1099cc 6 15).toInstrSpec (mov_r64_r64_effect_step 0x1099cc 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1099cf [0x48, 0x83, 0xC5, 0xC0] (fun s => s.RIP = 0x1099cf) (addR64Imm8Effect 0x1099cf 5 0xc0)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1099cf 5 0xc0).toInstrSpec (add_r64_imm8_effect_step 0x1099cf 0x48 0xc5 0xc0 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099cf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099d3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 58) (jcc_rel8_effect_step 0x1099d3 5 0xeb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1099cc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1099cc :=
  Rest.liftedBlock (rest_l1099cc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1099cc x hx)

theorem rest_l1099d5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1099d5 bytes_l1099d5) (entryMap (live .l1099d5))
      2 0x1099d5 bytes_l1099d5 b_l1099d5 := by
  have f0 : InstrSpec 0x1099d5 [0x49, 0x83, 0xE5, 0x30] (fun s => s.RIP = 0x1099d5) (andR64Imm8Effect 0x1099d5 13 0x30)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x1099d5 13 0x30).toInstrSpec (and_r64_imm8_effect_step 0x1099d5 0x49 0xe5 0x30 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 54) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099d9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 56) (jcc_rel32_effect_step 0x1099d9 4 0xcb) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1099d5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1099d5 :=
  Rest.liftedBlock (rest_l1099d5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1099d5 x hx)

theorem rest_l1099df [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1099df bytes_l1099df) (entryMap (live .l1099df))
      7 0x1099df bytes_l1099df b_l1099df := by
  have f0 : InstrSpec 0x1099df [0x48, 0xB8, 0xFC, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x07] (fun s => s.RIP = 0x1099df) (movR64Imm64Effect 0x1099df 0 0x7fffffffffffffc)
      [] [] [.reg 0, .rip] :=
    (movR64Imm64Effect_footprint 0x1099df 0 0x7fffffffffffffc).toInstrSpec (mov_r64_imm64_effect_step 0x1099df 0x48 0xb8 (by decide) (by decide) 0x7fffffffffffffc) pre_rip
  have f1 : InstrSpec 0x1099e9 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x1099e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1099e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1099e9 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x1099e9 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x1099e9 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1099ee [0x48, 0x21, 0xC1] (fun s => s.RIP = 0x1099ee) (andR64R64Effect 0x1099ee 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (andR64R64Effect_footprint 0x1099ee 1 0).toInstrSpec (and_r64_r64_effect_step 0x1099ee 0x48 0xc1 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1099f1 [0x48, 0xC1, 0xE1, 0x04] (fun s => s.RIP = 0x1099f1) (shlR64Effect 0x1099f1 4 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR64Effect_footprint 0x1099f1 4 1 4).toInstrSpec (shl_r64_imm8_effect_step 0x1099f1 0x48 0xe1 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1099f5 [0x48, 0x01, 0xCB] (fun s => s.RIP = 0x1099f5) (addR64R64Effect 0x1099f5 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x1099f5 3 1).toInstrSpec (add_r64_r64_effect_step 0x1099f5 0x48 0xcb (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1099f8 [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x1099f8) (xorR32R32Effect 0x1099f8 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1099f8 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x1099f8 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1099fb [0x4C, 0x8D, 0x7C, 0x24, 0x08] (fun s => s.RIP = 0x1099fb) (leaR64Effect 0x1099fb 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (leaR64Effect_footprint 0x1099fb 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x1099fb 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099e9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099ee) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099f1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099f5) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (3, 61), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099f8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 59), (3, 61), (4, 4), (5, 5), (12, 63), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1099fb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 59), (3, 61), (4, 4), (5, 5), (12, 63), (13, 13), (14, 14), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a00) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 67) (by decide) rfl

theorem block_l1099df [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1099df :=
  Rest.liftedBlock (rest_l1099df code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1099df x hx)

theorem rest_l109a00_1 [Bindings] (code : CodeMap) :
    Rest (n := 83) code lifted (codeRange 0x109a00 bytes_l109a00) [(0, 81), (1, 77), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      15 0x109a5b bytes_l109a00_1 b_l109a00_1 := by
  have f20 : InstrSpec 0x109a5b [0x0F, 0xB6, 0x4C, 0x24, 0x13] (LoadPre 0x109a5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x109a5b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a5b 5 1 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109a5b 5 1 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (movzx_r32_m8_effect_step 0x109a5b 1 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f21 : InstrSpec 0x109a60 [0x88, 0x4C, 0x24, 0x0C] (StorePre 0x109a60 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x109a60 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a60 4 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a60 4 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_effect_step 0x109a60 1 (by decide) (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f22 : InstrSpec 0x109a64 [0x88, 0x44, 0x24, 0x13] (StorePre 0x109a64 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x109a64 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a64 4 0 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a64 4 0 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (mov_m8_r8_effect_step 0x109a64 0 (by decide) (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x109a68 [0x0F, 0xB6, 0x44, 0x24, 0x0D] (LoadPre 0x109a68 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x109a68 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a68 5 0 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109a68 5 0 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_effect_step 0x109a68 0 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x109a6d [0x0F, 0xB6, 0x4C, 0x24, 0x12] (LoadPre 0x109a6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x109a6d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a6d 5 1 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109a6d 5 1 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (movzx_r32_m8_effect_step 0x109a6d 1 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f25 : InstrSpec 0x109a72 [0x88, 0x4C, 0x24, 0x0D] (StorePre 0x109a72 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x109a72 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a72 4 1 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a72 4 1 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_effect_step 0x109a72 1 (by decide) (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x109a76 [0x88, 0x44, 0x24, 0x12] (StorePre 0x109a76 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x109a76 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a76 4 0 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a76 4 0 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (mov_m8_r8_effect_step 0x109a76 0 (by decide) (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x109a7a [0x0F, 0xB6, 0x44, 0x24, 0x0E] (LoadPre 0x109a7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x109a7a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a7a 5 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109a7a 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m8_effect_step 0x109a7a 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x109a7f [0x0F, 0xB6, 0x4C, 0x24, 0x11] (LoadPre 0x109a7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x109a7f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a7f 5 1 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109a7f 5 1 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (movzx_r32_m8_effect_step 0x109a7f 1 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f29 : InstrSpec 0x109a84 [0x88, 0x4C, 0x24, 0x0E] (StorePre 0x109a84 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x109a84 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a84 4 1 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a84 4 1 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_effect_step 0x109a84 1 (by decide) (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f30 : InstrSpec 0x109a88 [0x88, 0x44, 0x24, 0x11] (StorePre 0x109a88 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x109a88 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a88 4 0 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a88 4 0 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (mov_m8_r8_effect_step 0x109a88 0 (by decide) (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x109a8c [0x66, 0xC1, 0x44, 0x24, 0x0F, 0x08] (StorePre 0x109a8c 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x109a8c + BitVec.ofNat 64 6)) 2) (rolMEffect 0x109a8c 6 16 (.sib 4 none 0 (.d8 0xf)) 8)
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (rolMEffect16_footprint 0x109a8c 6 (.sib 4 none 0 (.d8 0xf)) 8).toInstrSpec (rol_m16_imm8_effect_step 0x109a8c (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide) 0x8) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x109a92 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x109a92) (movR64R64Effect 0x109a92 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x109a92 7 14).toInstrSpec (mov_r64_r64_effect_step 0x109a92 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x109a95 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x109a95) (movR64R64Effect 0x109a95 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x109a95 6 15).toInstrSpec (mov_r64_r64_effect_step 0x109a95 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x109a98 [0xE8, 0x23, 0x9A, 0xFF, 0xFF] (PushPre 0x109a98 5) (callEffect (fun _ => 0x1034c0) 0x109a9d)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109a98 0x1034c0 0x109a9d).toInstrSpec (call_rel32_effect_step 0x109a98 0xffff9a23 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f20 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 81), (1, 83), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a60) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.exec (n := 85) (ρ' := [(0, 81), (1, 83), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a64) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 81), (1, 83), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a68) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 87), (1, 83), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a6d) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 87), (1, 89), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a72) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.exec (n := 91) (ρ' := [(0, 87), (1, 89), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a76) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 87), (1, 89), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a7a) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 93), (1, 89), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a7f) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f28 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 93), (1, 95), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a84) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 93), (1, 95), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a88) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 93), (1, 95), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a8c) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 93), (1, 95), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a92) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f32 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 93), (1, 95), (2, 67), (3, 3), (4, 4), (5, 5), (7, 100), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a95) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f33 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 93), (1, 95), (2, 67), (3, 3), (4, 4), (5, 5), (6, 102), (7, 100), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a98) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f34 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 93), (1, 95), (2, 67), (3, 3), (4, 104), (5, 5), (6, 102), (7, 100), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034c0) f34 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 106) (by decide) (by decide) rfl rfl

theorem rest_l109a00 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109a00 bytes_l109a00) (entryMap (live .l109a00))
      35 0x109a00 bytes_l109a00 b_l109a00 := by
  have f0 : InstrSpec 0x109a00 [0x4A, 0x8B, 0x04, 0x23] (LoadPre 0x109a00 (fun s => AddrMode.addr (.sib 3 (some 12) 0 .none) s (0x109a00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a00 0 (.sib 3 (some 12) 0 .none))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109a00 0 (.sib 3 (some 12) 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109a00 0x4a (by decide) 0 (.sib 3 (some 12) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x109a04 [0x4A, 0x8B, 0x4C, 0x23, 0x08] (LoadPre 0x109a04 (fun s => AddrMode.addr (.sib 3 (some 12) 0 (.d8 0x8)) s (0x109a04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109a04 1 (.sib 3 (some 12) 0 (.d8 0x8)))
      [.gpr 3, .gpr 12] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109a04 1 (.sib 3 (some 12) 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109a04 0x4a (by decide) 1 (.sib 3 (some 12) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109a09 [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x109a09 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109a09 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a09 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109a09 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109a09 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x109a0e [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x109a0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109a0e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a0e 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109a0e 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109a0e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x109a13 [0x0F, 0xB6, 0x4C, 0x24, 0x17] (LoadPre 0x109a13 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x109a13 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a13 5 1 (.sib 4 none 0 (.d8 0x17)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109a13 5 1 (.sib 4 none 0 (.d8 0x17))).toInstrSpec (movzx_r32_m8_effect_step 0x109a13 1 (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x109a18 [0x88, 0x4C, 0x24, 0x08] (StorePre 0x109a18 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109a18 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a18 4 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a18 4 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x109a18 1 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x109a1c [0x88, 0x44, 0x24, 0x17] (StorePre 0x109a1c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x109a1c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a1c 4 0 (.sib 4 none 0 (.d8 0x17)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a1c 4 0 (.sib 4 none 0 (.d8 0x17))).toInstrSpec (mov_m8_r8_effect_step 0x109a1c 0 (by decide) (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x109a20 [0x0F, 0xB6, 0x44, 0x24, 0x16] (LoadPre 0x109a20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x109a20 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a20 5 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109a20 5 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m8_effect_step 0x109a20 0 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x109a25 [0x0F, 0xB6, 0x4C, 0x24, 0x09] (LoadPre 0x109a25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x109a25 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a25 5 1 (.sib 4 none 0 (.d8 0x9)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109a25 5 1 (.sib 4 none 0 (.d8 0x9))).toInstrSpec (movzx_r32_m8_effect_step 0x109a25 1 (.sib 4 none 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x109a2a [0x0F, 0xB6, 0x54, 0x24, 0x0A] (LoadPre 0x109a2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x109a2a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a2a 5 2 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M8Effect_footprint 0x109a2a 5 2 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m8_effect_step 0x109a2a 2 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x109a2f [0x88, 0x44, 0x24, 0x09] (StorePre 0x109a2f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x109a2f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a2f 4 0 (.sib 4 none 0 (.d8 0x9)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a2f 4 0 (.sib 4 none 0 (.d8 0x9))).toInstrSpec (mov_m8_r8_effect_step 0x109a2f 0 (by decide) (.sib 4 none 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x109a33 [0x88, 0x4C, 0x24, 0x16] (StorePre 0x109a33 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x109a33 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a33 4 1 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a33 4 1 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m8_r8_effect_step 0x109a33 1 (by decide) (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x109a37 [0x0F, 0xB6, 0x44, 0x24, 0x14] (LoadPre 0x109a37 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x109a37 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a37 5 0 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109a37 5 0 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m8_effect_step 0x109a37 0 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x109a3c [0x0F, 0xB6, 0x4C, 0x24, 0x15] (LoadPre 0x109a3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x109a3c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a3c 5 1 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109a3c 5 1 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (movzx_r32_m8_effect_step 0x109a3c 1 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x109a41 [0x88, 0x4C, 0x24, 0x0A] (StorePre 0x109a41 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x109a41 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a41 4 1 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a41 4 1 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m8_r8_effect_step 0x109a41 1 (by decide) (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x109a45 [0x88, 0x54, 0x24, 0x15] (StorePre 0x109a45 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x109a45 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a45 4 2 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a45 4 2 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_m8_r8_effect_step 0x109a45 2 (by decide) (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x109a49 [0x0F, 0xB6, 0x4C, 0x24, 0x0B] (LoadPre 0x109a49 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x109a49 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a49 5 1 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109a49 5 1 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_effect_step 0x109a49 1 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x109a4e [0x88, 0x44, 0x24, 0x0B] (StorePre 0x109a4e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x109a4e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a4e 4 0 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a4e 4 0 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_effect_step 0x109a4e 0 (by decide) (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x109a52 [0x88, 0x4C, 0x24, 0x14] (StorePre 0x109a52 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x109a52 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109a52 4 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109a52 4 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m8_r8_effect_step 0x109a52 1 (by decide) (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x109a56 [0x0F, 0xB6, 0x44, 0x24, 0x0C] (LoadPre 0x109a56 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x109a56 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109a56 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109a56 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x109a56 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a04) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a09) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a0e) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a13) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a18) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a1c) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a20) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a25) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 63), (1, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a2a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 63), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a2f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 63), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a33) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 63), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a37) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (1, 65), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a3c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (1, 73), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a41) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 71), (1, 73), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a45) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 71), (1, 73), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a49) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (1, 77), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a4e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 71), (1, 77), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a52) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 71), (1, 77), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a56) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (1, 77), (2, 67), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109a5b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109a00_1 code

theorem block_l109a00 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109a00 :=
  Rest.liftedBlock (rest_l109a00 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109a00 x hx)

theorem rest_l109a9d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109a9d bytes_l109a9d) (entryMap (live .l109a9d))
      3 0x109a9d bytes_l109a9d b_l109a9d := by
  have f0 : InstrSpec 0x109a9d [0x49, 0x83, 0xC4, 0x10] (fun s => s.RIP = 0x109a9d) (addR64Imm8Effect 0x109a9d 12 0x10)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109a9d 12 0x10).toInstrSpec (add_r64_imm8_effect_step 0x109a9d 0x49 0xc4 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109aa1 [0x4D, 0x39, 0xE5] (fun s => s.RIP = 0x109aa1) (cmpR64R64Effect 0x109aa1 13 12)
      [.gpr 13, .gpr 12] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x109aa1 13 12).toInstrSpec (cmp_r64_r64_effect_step 0x109aa1 0x4d 0xe5 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aa1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aa4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 57) (jcc_rel32_effect_step 0x109aa4 5 0xffffff56) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l109a9d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109a9d :=
  Rest.liftedBlock (rest_l109a9d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109a9d x hx)

theorem rest_l109aaa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109aaa bytes_l109aaa) (entryMap (live .l109aaa))
      8 0x109aaa bytes_l109aaa b_l109aaa := by
  have f0 : InstrSpec 0x109aaa [0x48, 0x83, 0xC4, 0x28] (fun s => s.RIP = 0x109aaa) (addR64Imm8Effect 0x109aaa 4 0x28)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x109aaa 4 0x28).toInstrSpec (add_r64_imm8_effect_step 0x109aaa 0x48 0xc4 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109aae [0x5B] (PopPre 0x109aae) (popR64Effect 0x109aae 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109aae 1 3).toInstrSpec (pop_r64_effect_step 0x109aae 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x109aaf [0x41, 0x5C] (PopPre 0x109aaf) (popR64Effect 0x109aaf 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109aaf 2 12).toInstrSpec (pop_r64_rex_effect_step 0x109aaf 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x109ab1 [0x41, 0x5D] (PopPre 0x109ab1) (popR64Effect 0x109ab1 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109ab1 2 13).toInstrSpec (pop_r64_rex_effect_step 0x109ab1 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x109ab3 [0x41, 0x5E] (PopPre 0x109ab3) (popR64Effect 0x109ab3 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109ab3 2 14).toInstrSpec (pop_r64_rex_effect_step 0x109ab3 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x109ab5 [0x41, 0x5F] (PopPre 0x109ab5) (popR64Effect 0x109ab5 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109ab5 2 15).toInstrSpec (pop_r64_rex_effect_step 0x109ab5 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x109ab7 [0x5D] (PopPre 0x109ab7) (popR64Effect 0x109ab7 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x109ab7 1 5).toInstrSpec (pop_r64_effect_step 0x109ab7 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x109ab8 [0xC3] (RetPre 0x109ab8) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109ab8).toInstrSpec (ret_effect_step 0x109ab8) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aae) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aaf) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ab1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ab3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ab5) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ab7) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ab8) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l109aaa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109aaa :=
  Rest.liftedBlock (rest_l109aaa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109aaa x hx)

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

theorem_by block_l103f30_eval :
    program.runBlock (dialect code) ⟨.l103f30, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103f3e_eval :
    program.runBlock (dialect code) ⟨.l103f3e, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103f4b_eval :
    program.runBlock (dialect code) ⟨.l103f4b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103f62_eval :
    program.runBlock (dialect code) ⟨.l103f62, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103f79_eval :
    program.runBlock (dialect code) ⟨.l103f79, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103f8c_eval :
    program.runBlock (dialect code) ⟨.l103f8c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103f9f_eval :
    program.runBlock (dialect code) ⟨.l103f9f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103fb2_eval :
    program.runBlock (dialect code) ⟨.l103fb2, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103fc5_eval :
    program.runBlock (dialect code) ⟨.l103fc5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103fd4_eval :
    program.runBlock (dialect code) ⟨.l103fd4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103fdd_eval :
    program.runBlock (dialect code) ⟨.l103fdd, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103fe8_eval :
    program.runBlock (dialect code) ⟨.l103fe8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103ff7_eval :
    program.runBlock (dialect code) ⟨.l103ff7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l103ffa_eval :
    program.runBlock (dialect code) ⟨.l103ffa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l104009_eval :
    program.runBlock (dialect code) ⟨.l104009, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109980_eval :
    program.runBlock (dialect code) ⟨.l109980, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1099b4_eval :
    program.runBlock (dialect code) ⟨.l1099b4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1099c0_eval :
    program.runBlock (dialect code) ⟨.l1099c0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1099cc_eval :
    program.runBlock (dialect code) ⟨.l1099cc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1099d5_eval :
    program.runBlock (dialect code) ⟨.l1099d5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1099df_eval :
    program.runBlock (dialect code) ⟨.l1099df, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109a00_eval :
    program.runBlock (dialect code) ⟨.l109a00, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109a9d_eval :
    program.runBlock (dialect code) ⟨.l109a9d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109aaa_eval :
    program.runBlock (dialect code) ⟨.l109aaa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
