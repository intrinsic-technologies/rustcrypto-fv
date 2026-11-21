import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import X86Proofs.Instructions.Branch.Triple
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

theorem rest_l1012b0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1012b0 bytes_l1012b0) (entryMap (live .l1012b0))
      12 0x1012b0 bytes_l1012b0 b_l1012b0 := by
  have f0 : InstrSpec 0x1012b0 [0x44, 0x01, 0xCF] (fun s => s.RIP = 0x1012b0) (addR32R32Effect 0x1012b0 3 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1012b0 3 7 9).toInstrSpec (add_r32_r32_rex_effect_step 0x1012b0 0x44 0xcf (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1012b3 [0x41, 0x31, 0xF8] (fun s => s.RIP = 0x1012b3) (xorR32R32Effect 0x1012b3 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1012b3 3 8 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x1012b3 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1012b6 [0x41, 0xC1, 0xC0, 0x10] (fun s => s.RIP = 0x1012b6) (rolR32Effect 0x1012b6 4 8 16)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR32Effect_footprint 0x1012b6 4 8 16).toInstrSpec (rol_r32_imm8_rex_effect_step 0x1012b6 0x41 0xc0 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1012ba [0x45, 0x01, 0xC2] (fun s => s.RIP = 0x1012ba) (addR32R32Effect 0x1012ba 3 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1012ba 3 10 8).toInstrSpec (add_r32_r32_rex_effect_step 0x1012ba 0x45 0xc2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1012bd [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x1012bd) (xorR32R32Effect 0x1012bd 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1012bd 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1012bd 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1012c0 [0x41, 0xC1, 0xC1, 0x0C] (fun s => s.RIP = 0x1012c0) (rolR32Effect 0x1012c0 4 9 12)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR32Effect_footprint 0x1012c0 4 9 12).toInstrSpec (rol_r32_imm8_rex_effect_step 0x1012c0 0x41 0xc1 0xc (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1012c4 [0x44, 0x01, 0xCF] (fun s => s.RIP = 0x1012c4) (addR32R32Effect 0x1012c4 3 7 9)
      [.gpr 7, .gpr 9] [] [.reg 7, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1012c4 3 7 9).toInstrSpec (add_r32_r32_rex_effect_step 0x1012c4 0x44 0xcf (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1012c7 [0x41, 0x31, 0xF8] (fun s => s.RIP = 0x1012c7) (xorR32R32Effect 0x1012c7 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1012c7 3 8 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x1012c7 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1012ca [0x41, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x1012ca) (rolR32Effect 0x1012ca 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR32Effect_footprint 0x1012ca 4 8 8).toInstrSpec (rol_r32_imm8_rex_effect_step 0x1012ca 0x41 0xc0 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1012ce [0x45, 0x01, 0xC2] (fun s => s.RIP = 0x1012ce) (addR32R32Effect 0x1012ce 3 10 8)
      [.gpr 10, .gpr 8] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1012ce 3 10 8).toInstrSpec (add_r32_r32_rex_effect_step 0x1012ce 0x45 0xc2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1012d1 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x1012d1) (xorR32R32Effect 0x1012d1 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1012d1 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1012d1 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1012d4 [0x41, 0xC1, 0xC1, 0x07] (fun s => s.RIP = 0x1012d4) (rolR32Effect 0x1012d4 4 9 7)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR32Effect_footprint 0x1012d4 4 9 7).toInstrSpec (rol_r32_imm8_rex_effect_step 0x1012d4 0x41 0xc1 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012b3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012b6) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012ba) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 57), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012bd) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 57), (9, 61), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012c0) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 57), (9, 63), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012c4) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 57), (9, 63), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012c7) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 67), (9, 63), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012ca) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 69), (9, 63), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012ce) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 69), (9, 63), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012d1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 69), (9, 73), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012d4) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 69), (9, 75), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012d8) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l1012b0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1012b0 :=
  Rest.liftedBlock (rest_l1012b0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1012b0 x hx)

theorem rest_l1012d8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1012d8 bytes_l1012d8) (entryMap (live .l1012d8))
      2 0x1012d8 bytes_l1012d8 b_l1012d8 := by
  have f0 : InstrSpec 0x1012d8 [0x48, 0xFF, 0x4C, 0x24, 0x58] (StorePre 0x1012d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1012d8 + BitVec.ofNat 64 5)) 8) (decMEffect 0x1012d8 5 64 (.sib 4 none 0 (.d8 0x58)))
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (decMEffect64_footprint 0x1012d8 5 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (dec_m64_effect_step 0x1012d8 0x48 (by decide) (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.fresh (n := 53) f0 .ZF (fun _ => rfl) (decMEffect64_fresh 0x1012d8 5 (.sib 4 none 0 (.d8 0x58)) _ (.tail _ (.tail _ (.head _)))) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012dd) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1012dd 5 0xfffffe9d) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1012d8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1012d8 :=
  Rest.liftedBlock (rest_l1012d8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1012d8 x hx)

theorem rest_l1012e3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1012e3 bytes_l1012e3) (entryMap (live .l1012e3))
      20 0x1012e3 bytes_l1012e3 b_l1012e3 := by
  have f0 : InstrSpec 0x1012e3 [0x8B, 0x5C, 0x24, 0x08] (LoadPre 0x1012e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1012e3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1012e3 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x1012e3 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x1012e3 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1012e7 [0x03, 0x5C, 0x24, 0x38] (LoadPre 0x1012e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1012e7 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x1012e7 4 3 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (addR32M32Effect_footprint 0x1012e7 4 3 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (add_r32_m32_effect_step 0x1012e7 3 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1012eb [0x89, 0x5C, 0x24, 0x08] (StorePre 0x1012eb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1012eb + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1012eb 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1012eb 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x1012eb 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x1012ef [0x44, 0x03, 0x6C, 0x24, 0x60] (LoadPre 0x1012ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1012ef + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x1012ef 5 13 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 13, .gpr 4] [] [.reg 13, .flags, .rip] :=
    (addR32M32Effect_footprint 0x1012ef 5 13 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (add_r32_m32_rex_effect_step 0x1012ef 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1012f4 [0x44, 0x89, 0x6C, 0x24, 0x14] (StorePre 0x1012f4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1012f4 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1012f4 13 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1012f4 13 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_effect_step 0x1012f4 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x1012f9 [0x03, 0x44, 0x24, 0x68] (LoadPre 0x1012f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1012f9 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x1012f9 4 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.reg 0, .flags, .rip] :=
    (addR32M32Effect_footprint 0x1012f9 4 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (add_r32_m32_effect_step 0x1012f9 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1012fd [0x03, 0x7C, 0x24, 0x0C] (LoadPre 0x1012fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1012fd + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x1012fd 4 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 7, .gpr 4] [] [.reg 7, .flags, .rip] :=
    (addR32M32Effect_footprint 0x1012fd 4 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (add_r32_m32_effect_step 0x1012fd 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101301 [0x44, 0x03, 0x4C, 0x24, 0x50] (LoadPre 0x101301 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101301 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x101301 5 9 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 9, .gpr 4] [] [.reg 9, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101301 5 9 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (add_r32_m32_rex_effect_step 0x101301 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101306 [0x03, 0x6C, 0x24, 0x70] (LoadPre 0x101306 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101306 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101306 4 5 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 5, .gpr 4] [] [.reg 5, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101306 4 5 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (add_r32_m32_effect_step 0x101306 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10130a [0x44, 0x03, 0x7C, 0x24, 0x3C] (LoadPre 0x10130a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x10130a + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x10130a 5 15 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 15, .gpr 4] [] [.reg 15, .flags, .rip] :=
    (addR32M32Effect_footprint 0x10130a 5 15 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (add_r32_m32_rex_effect_step 0x10130a 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x10130f [0x03, 0x74, 0x24, 0x10] (LoadPre 0x10130f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10130f + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x10130f 4 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.reg 6, .flags, .rip] :=
    (addR32M32Effect_footprint 0x10130f 4 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (add_r32_m32_effect_step 0x10130f 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x101313 [0x8B, 0x5C, 0x24, 0x04] (LoadPre 0x101313 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x101313 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x101313 3 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x101313 3 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x101313 3 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x101317 [0x03, 0x5C, 0x24, 0x18] (LoadPre 0x101317 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101317 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101317 4 3 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 3, .gpr 4] [] [.reg 3, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101317 4 3 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (add_r32_m32_effect_step 0x101317 3 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10131b [0x89, 0x5C, 0x24, 0x04] (StorePre 0x10131b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10131b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10131b 3 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10131b 3 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x10131b 3 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x10131f [0x44, 0x03, 0x54, 0x24, 0x1C] (LoadPre 0x10131f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10131f + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x10131f 5 10 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 10, .gpr 4] [] [.reg 10, .flags, .rip] :=
    (addR32M32Effect_footprint 0x10131f 5 10 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (add_r32_m32_rex_effect_step 0x10131f 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x101324 [0x44, 0x03, 0x74, 0x24, 0x20] (LoadPre 0x101324 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101324 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x101324 5 14 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 14, .gpr 4] [] [.reg 14, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101324 5 14 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (add_r32_m32_rex_effect_step 0x101324 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101329 [0x44, 0x03, 0x64, 0x24, 0x24] (LoadPre 0x101329 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x101329 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x101329 5 12 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 12, .gpr 4] [] [.reg 12, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101329 5 12 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (add_r32_m32_rex_effect_step 0x101329 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10132e [0x03, 0x54, 0x24, 0x28] (LoadPre 0x10132e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10132e + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x10132e 4 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 2, .gpr 4] [] [.reg 2, .flags, .rip] :=
    (addR32M32Effect_footprint 0x10132e 4 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (add_r32_m32_effect_step 0x10132e 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x101332 [0x44, 0x03, 0x44, 0x24, 0x2C] (LoadPre 0x101332 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x101332 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x101332 5 8 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 8, .gpr 4] [] [.reg 8, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101332 5 8 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (add_r32_m32_rex_effect_step 0x101332 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x101337 [0x44, 0x03, 0x5C, 0x24, 0x30] (LoadPre 0x101337 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x101337 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x101337 5 11 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 11, .gpr 4] [] [.reg 11, .flags, .rip] :=
    (addR32M32Effect_footprint 0x101337 5 11 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (add_r32_m32_rex_effect_step 0x101337 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012e7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012eb) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012ef) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012f4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012f9) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012fd) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101301) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 55), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 65), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101306) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 55), (4, 4), (5, 67), (6, 6), (7, 63), (8, 8), (9, 65), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10130a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 55), (4, 4), (5, 67), (6, 6), (7, 63), (8, 8), (9, 65), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10130f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 55), (4, 4), (5, 67), (6, 71), (7, 63), (8, 8), (9, 65), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101313) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 73), (4, 4), (5, 67), (6, 71), (7, 63), (8, 8), (9, 65), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101317) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 75), (4, 4), (5, 67), (6, 71), (7, 63), (8, 8), (9, 65), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10131b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 75), (4, 4), (5, 67), (6, 71), (7, 63), (8, 8), (9, 65), (10, 10), (11, 11), (12, 12), (13, 58), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10131f) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 75), (4, 4), (5, 67), (6, 71), (7, 63), (8, 8), (9, 65), (10, 78), (11, 11), (12, 12), (13, 58), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101324) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 75), (4, 4), (5, 67), (6, 71), (7, 63), (8, 8), (9, 65), (10, 78), (11, 11), (12, 12), (13, 58), (14, 80), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101329) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 61), (1, 1), (2, 2), (3, 75), (4, 4), (5, 67), (6, 71), (7, 63), (8, 8), (9, 65), (10, 78), (11, 11), (12, 82), (13, 58), (14, 80), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10132e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 61), (1, 1), (2, 84), (3, 75), (4, 4), (5, 67), (6, 71), (7, 63), (8, 8), (9, 65), (10, 78), (11, 11), (12, 82), (13, 58), (14, 80), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101332) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 61), (1, 1), (2, 84), (3, 75), (4, 4), (5, 67), (6, 71), (7, 63), (8, 86), (9, 65), (10, 78), (11, 11), (12, 82), (13, 58), (14, 80), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101337) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 61), (1, 1), (2, 84), (3, 75), (4, 4), (5, 67), (6, 71), (7, 63), (8, 86), (9, 65), (10, 78), (11, 88), (12, 82), (13, 58), (14, 80), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10133c) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 90) (by decide) rfl

theorem block_l1012e3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1012e3 :=
  Rest.liftedBlock (rest_l1012e3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1012e3 x hx)

theorem rest_l10133c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10133c bytes_l10133c) (entryMap (live .l10133c))
      20 0x10133c bytes_l10133c b_l10133c := by
  have f0 : InstrSpec 0x10133c [0x8B, 0x5C, 0x24, 0x34] (LoadPre 0x10133c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x10133c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10133c 3 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x10133c 3 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x10133c 3 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101340 [0x01, 0xD9] (fun s => s.RIP = 0x101340) (addR32R32Effect 0x101340 2 1 3)
      [.gpr 1, .gpr 3] [] [.reg 1, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101340 2 1 3).toInstrSpec (add_r32_r32_effect_step 0x101340 0xd9 (by decide)) pre_rip
  have f2 : InstrSpec 0x101342 [0xFF, 0xC3] (fun s => s.RIP = 0x101342) (incR32Effect 0x101342 2 3)
      [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 3, .flags, .rip] :=
    (incR32Effect_footprint 0x101342 2 3).toInstrSpec (inc_r32_effect_step 0x101342 0xc3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101344 [0x41, 0x89, 0xDD] (fun s => s.RIP = 0x101344) (movR32R32Effect 0x101344 3 13 3)
      [.gpr 3] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x101344 3 13 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x101344 0x41 0xdd (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101347 [0x48, 0x8B, 0x5C, 0x24, 0x48] (LoadPre 0x101347 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101347 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101347 3 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x101347 3 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x101347 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10134c [0x44, 0x89, 0x6B, 0x30] (StorePre 0x10134c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x10134c + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10134c 13 (.base 3 (.d8 0x30)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x10134c 13 (.base 3 (.d8 0x30))).toInstrSpec (mov_m32_r32_effect_step 0x10134c 0x44 (by decide) 5 (.base 3 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101350 [0x8B, 0x5C, 0x24, 0x08] (LoadPre 0x101350 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101350 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x101350 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x101350 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x101350 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101354 [0x4C, 0x8B, 0x6C, 0x24, 0x48] (LoadPre 0x101354 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101354 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101354 13 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR64M64Effect_footprint 0x101354 13 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x101354 0x4c (by decide) 5 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101359 [0x41, 0x89, 0x5D, 0x40] (StorePre 0x101359 4 (fun s => AddrMode.addr (.base 13 (.d8 0x40)) s (0x101359 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101359 3 (.base 13 (.d8 0x40)))
      [.gpr 3, .gpr 13] [] [.rip] :=
    (movM32R32Effect_footprint 0x101359 3 (.base 13 (.d8 0x40))).toInstrSpec (mov_m32_r32_effect_step 0x101359 0x41 (by decide) 3 (.base 13 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x10135d [0x48, 0x8B, 0x5C, 0x24, 0x48] (LoadPre 0x10135d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10135d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10135d 3 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10135d 3 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x10135d 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101362 [0x44, 0x8B, 0x6C, 0x24, 0x14] (LoadPre 0x101362 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x101362 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x101362 13 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x101362 13 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_effect_step 0x101362 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x101367 [0x44, 0x89, 0x6B, 0x44] (StorePre 0x101367 4 (fun s => AddrMode.addr (.base 3 (.d8 0x44)) s (0x101367 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101367 13 (.base 3 (.d8 0x44)))
      [.gpr 13, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x101367 13 (.base 3 (.d8 0x44))).toInstrSpec (mov_m32_r32_effect_step 0x101367 0x44 (by decide) 5 (.base 3 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10136b [0x89, 0x43, 0x48] (StorePre 0x10136b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x10136b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10136b 0 (.base 3 (.d8 0x48)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10136b 0 (.base 3 (.d8 0x48))).toInstrSpec (mov_m32_r32_low_effect_step 0x10136b 0 (.base 3 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10136e [0x89, 0x7B, 0x4C] (StorePre 0x10136e 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4c)) s (0x10136e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10136e 7 (.base 3 (.d8 0x4c)))
      [.gpr 7, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10136e 7 (.base 3 (.d8 0x4c))).toInstrSpec (mov_m32_r32_low_effect_step 0x10136e 7 (.base 3 (.d8 0x4c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x101371 [0x44, 0x89, 0x4B, 0x50] (StorePre 0x101371 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x101371 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101371 9 (.base 3 (.d8 0x50)))
      [.gpr 9, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x101371 9 (.base 3 (.d8 0x50))).toInstrSpec (mov_m32_r32_effect_step 0x101371 0x44 (by decide) 1 (.base 3 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x101375 [0x49, 0x89, 0xD9] (fun s => s.RIP = 0x101375) (movR64R64Effect 0x101375 9 3)
      [.gpr 3] [] [.reg 9, .rip] :=
    (movR64R64Effect_footprint 0x101375 9 3).toInstrSpec (mov_r64_r64_effect_step 0x101375 0x49 0xd9 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x101378 [0x89, 0x6B, 0x54] (StorePre 0x101378 3 (fun s => AddrMode.addr (.base 3 (.d8 0x54)) s (0x101378 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101378 5 (.base 3 (.d8 0x54)))
      [.gpr 5, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101378 5 (.base 3 (.d8 0x54))).toInstrSpec (mov_m32_r32_low_effect_step 0x101378 5 (.base 3 (.d8 0x54)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x10137b [0x44, 0x89, 0x7B, 0x58] (StorePre 0x10137b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x10137b + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10137b 15 (.base 3 (.d8 0x58)))
      [.gpr 15, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x10137b 15 (.base 3 (.d8 0x58))).toInstrSpec (mov_m32_r32_effect_step 0x10137b 0x44 (by decide) 7 (.base 3 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10137f [0x89, 0x73, 0x5C] (StorePre 0x10137f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x5c)) s (0x10137f + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10137f 6 (.base 3 (.d8 0x5c)))
      [.gpr 6, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10137f 6 (.base 3 (.d8 0x5c))).toInstrSpec (mov_m32_r32_low_effect_step 0x10137f 6 (.base 3 (.d8 0x5c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x101382 [0x8B, 0x44, 0x24, 0x04] (LoadPre 0x101382 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x101382 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x101382 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x101382 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x101382 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101340) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101342) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101344) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101347) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10134c) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 61), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101350) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 64), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101354) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 64), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 66), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101359) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 64), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 66), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10135d) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 66), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101362) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101367) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10136b) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10136e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101371) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101375) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 77), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101378) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 77), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10137b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 77), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10137f) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 77), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101382) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f19 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 82), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 77), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101386) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 84) (by decide) rfl

theorem block_l10133c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10133c :=
  Rest.liftedBlock (rest_l10133c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10133c x hx)

theorem rest_l101386 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101386 bytes_l101386) (entryMap (live .l101386))
      14 0x101386 bytes_l101386 b_l101386 := by
  have f0 : InstrSpec 0x101386 [0x89, 0x43, 0x60] (StorePre 0x101386 3 (fun s => AddrMode.addr (.base 3 (.d8 0x60)) s (0x101386 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101386 0 (.base 3 (.d8 0x60)))
      [.gpr 0, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101386 0 (.base 3 (.d8 0x60))).toInstrSpec (mov_m32_r32_low_effect_step 0x101386 0 (.base 3 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101389 [0x44, 0x89, 0x53, 0x64] (StorePre 0x101389 4 (fun s => AddrMode.addr (.base 3 (.d8 0x64)) s (0x101389 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101389 10 (.base 3 (.d8 0x64)))
      [.gpr 10, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x101389 10 (.base 3 (.d8 0x64))).toInstrSpec (mov_m32_r32_effect_step 0x101389 0x44 (by decide) 2 (.base 3 (.d8 0x64)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10138d [0x44, 0x89, 0x73, 0x68] (StorePre 0x10138d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x68)) s (0x10138d + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10138d 14 (.base 3 (.d8 0x68)))
      [.gpr 14, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x10138d 14 (.base 3 (.d8 0x68))).toInstrSpec (mov_m32_r32_effect_step 0x10138d 0x44 (by decide) 6 (.base 3 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101391 [0x44, 0x89, 0x63, 0x6C] (StorePre 0x101391 4 (fun s => AddrMode.addr (.base 3 (.d8 0x6c)) s (0x101391 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101391 12 (.base 3 (.d8 0x6c)))
      [.gpr 12, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x101391 12 (.base 3 (.d8 0x6c))).toInstrSpec (mov_m32_r32_effect_step 0x101391 0x44 (by decide) 4 (.base 3 (.d8 0x6c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x101395 [0x89, 0x4B, 0x70] (StorePre 0x101395 3 (fun s => AddrMode.addr (.base 3 (.d8 0x70)) s (0x101395 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101395 1 (.base 3 (.d8 0x70)))
      [.gpr 1, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101395 1 (.base 3 (.d8 0x70))).toInstrSpec (mov_m32_r32_low_effect_step 0x101395 1 (.base 3 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x101398 [0x89, 0x53, 0x74] (StorePre 0x101398 3 (fun s => AddrMode.addr (.base 3 (.d8 0x74)) s (0x101398 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101398 2 (.base 3 (.d8 0x74)))
      [.gpr 2, .gpr 3] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101398 2 (.base 3 (.d8 0x74))).toInstrSpec (mov_m32_r32_low_effect_step 0x101398 2 (.base 3 (.d8 0x74)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10139b [0x44, 0x89, 0x43, 0x78] (StorePre 0x10139b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x78)) s (0x10139b + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10139b 8 (.base 3 (.d8 0x78)))
      [.gpr 8, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x10139b 8 (.base 3 (.d8 0x78))).toInstrSpec (mov_m32_r32_effect_step 0x10139b 0x44 (by decide) 0 (.base 3 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10139f [0x44, 0x89, 0x5B, 0x7C] (StorePre 0x10139f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x7c)) s (0x10139f + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10139f 11 (.base 3 (.d8 0x7c)))
      [.gpr 11, .gpr 3] [] [.rip] :=
    (movM32R32Effect_footprint 0x10139f 11 (.base 3 (.d8 0x7c))).toInstrSpec (mov_m32_r32_effect_step 0x10139f 0x44 (by decide) 3 (.base 3 (.d8 0x7c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x1013a3 [0x4C, 0x8B, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x1013a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1013a3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013a3 10 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR64M64Effect_footprint 0x1013a3 10 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x1013a3 0x4c (by decide) 2 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1013ab [0x44, 0x89, 0xD0] (fun s => s.RIP = 0x1013ab) (movR32R32Effect 0x1013ab 3 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1013ab 3 0 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x1013ab 0x44 0xd0 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1013ae [0x83, 0xE0, 0x03] (fun s => s.RIP = 0x1013ae) (andR32Imm8Effect 0x1013ae 3 0 0x3)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1013ae 3 0 0x3).toInstrSpec (and_r32_imm8_effect_step 0x1013ae 0xe0 0x3 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1013b1 [0x4C, 0x8B, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x1013b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1013b1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013b1 14 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64M64Effect_footprint 0x1013b1 14 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x1013b1 0x4c (by decide) 6 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x1013b9 [0x41, 0x83, 0xFE, 0x04] (fun s => s.RIP = 0x1013b9) (cmpR32Imm8Effect 0x1013b9 4 14 0x4)
      [.gpr 14] [] [.flags, .rip] :=
    (cmpR32Imm8Effect_footprint 0x1013b9 4 14 0x4).toInstrSpec (cmp_r32_imm8_rex_effect_step 0x1013b9 0x41 0xfe 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101389) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10138d) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101391) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101395) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101398) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10139b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10139f) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013a3) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f8 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013ab) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 63), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013ae) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013b1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f11 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (14, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013b9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f12 (.flag .CF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (14, 67), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013bd) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 71) (jcc_rel8_effect_step 0x1013bd 3 0x24) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101386 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101386 :=
  Rest.liftedBlock (rest_l101386 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101386 x hx)

theorem rest_l1013bf [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1013bf bytes_l1013bf) (entryMap (live .l1013bf))
      6 0x1013bf bytes_l1013bf b_l1013bf := by
  have f0 : InstrSpec 0x1013bf [0x31, 0xF6] (fun s => s.RIP = 0x1013bf) (xorR32R32Effect 0x1013bf 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1013bf 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x1013bf 0xf6 (by decide)) pre_rip
  have f1 : InstrSpec 0x1013c1 [0x4C, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x1013c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1013c1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013c1 8 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1013c1 8 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x1013c1 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1013c9 [0x4C, 0x8B, 0x9C, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x1013c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1013c9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013c9 11 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1013c9 11 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x1013c9 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1013d1 [0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x1013d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1013d1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013d1 3 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x1013d1 3 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x1013d1 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1013d9 [0x4C, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x1013d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1013d9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1013d9 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1013d9 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1013d9 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (2, 2), (4, 4), (6, 53), (7, 7), (9, 9), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (2, 2), (4, 4), (6, 53), (7, 7), (8, 55), (9, 9), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013c9) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (2, 2), (4, 4), (6, 53), (7, 7), (8, 55), (9, 9), (11, 57), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013d1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 4), (6, 53), (7, 7), (8, 55), (9, 9), (11, 57), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013d9) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 2), (3, 59), (4, 4), (6, 53), (7, 7), (8, 55), (9, 9), (11, 57), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013de) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 63) (jmp_rel32_effect_step 0x1013de 0x89 (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem block_l1013bf [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1013bf :=
  Rest.liftedBlock (rest_l1013bf code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1013bf x hx)

theorem rest_l1013e3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1013e3 bytes_l1013e3) (entryMap (live .l1013e3))
      12 0x1013e3 bytes_l1013e3 b_l1013e3 := by
  have f0 : InstrSpec 0x1013e3 [0x41, 0x83, 0xE2, 0x3C] (fun s => s.RIP = 0x1013e3) (andR32Imm8Effect 0x1013e3 4 10 0x3c)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm8Effect_footprint 0x1013e3 4 10 0x3c).toInstrSpec (and_r32_imm8_rex_effect_step 0x1013e3 0x41 0xe2 0x3c (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1013e7 [0x4C, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00] (LoadPre 0x1013e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1013e7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013e7 8 (.sib 4 none 0 (.d32 0x98)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR64M64Effect_footprint 0x1013e7 8 (.sib 4 none 0 (.d32 0x98))).toInstrSpec (mov_r64_m64_effect_step 0x1013e7 0x4c (by decide) 0 (.sib 4 none 0 (.d32 0x98)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1013ef [0x4C, 0x8B, 0x7C, 0x24, 0x40] (LoadPre 0x1013ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1013ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1013ef 15 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1013ef 15 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_r64_m64_effect_step 0x1013ef 0x4c (by decide) 7 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1013f4 [0x4B, 0x8D, 0x14, 0x38] (fun s => s.RIP = 0x1013f4) (leaR64Effect 0x1013f4 2 (.sib 8 (some 15) 0 .none))
      [.gpr 8, .gpr 15] [] [.reg 2, .rip] :=
    (leaR64Effect_footprint 0x1013f4 2 (.sib 8 (some 15) 0 .none)).toInstrSpec (lea_r64_effect_step 0x1013f4 0x4b (by decide) 2 (.sib 8 (some 15) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1013f8 [0x4C, 0x8B, 0x9C, 0x24, 0x90, 0x00, 0x00, 0x00] (LoadPre 0x1013f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1013f8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013f8 11 (.sib 4 none 0 (.d32 0x90)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1013f8 11 (.sib 4 none 0 (.d32 0x90))).toInstrSpec (mov_r64_m64_effect_step 0x1013f8 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x101400 [0x49, 0x8D, 0x0C, 0x13] (fun s => s.RIP = 0x101400) (leaR64Effect 0x101400 1 (.sib 11 (some 2) 0 .none))
      [.gpr 11, .gpr 2] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x101400 1 (.sib 11 (some 2) 0 .none)).toInstrSpec (lea_r64_effect_step 0x101400 0x49 (by decide) 1 (.sib 11 (some 2) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101404 [0x48, 0x83, 0xC1, 0x03] (fun s => s.RIP = 0x101404) (addR64Imm8Effect 0x101404 1 0x3)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x101404 1 0x3).toInstrSpec (add_r64_imm8_effect_step 0x101404 0x48 0xc1 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101408 [0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00] (LoadPre 0x101408 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101408 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101408 3 (.sib 4 none 0 (.d32 0x88)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x101408 3 (.sib 4 none 0 (.d32 0x88))).toInstrSpec (mov_r64_m64_effect_step 0x101408 0x48 (by decide) 3 (.sib 4 none 0 (.d32 0x88)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101410 [0x48, 0x01, 0xDA] (fun s => s.RIP = 0x101410) (addR64R64Effect 0x101410 2 3)
      [.gpr 2, .gpr 3] [] [.reg 2, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101410 2 3).toInstrSpec (add_r64_r64_effect_step 0x101410 0x48 0xda (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101413 [0x48, 0x83, 0xC2, 0x03] (fun s => s.RIP = 0x101413) (addR64Imm8Effect 0x101413 2 0x3)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x101413 2 0x3).toInstrSpec (add_r64_imm8_effect_step 0x101413 0x48 0xc2 0x3 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101417 [0x31, 0xF6] (fun s => s.RIP = 0x101417) (xorR32R32Effect 0x101417 2 6 6)
      [.gpr 6, .gpr 6] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101417 2 6 6).toInstrSpec (xor_r32_r32_effect_step 0x101417 0xf6 (by decide)) pre_rip
  have f11 : InstrSpec 0x101419 [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101419) (fun _ => nopEffect 0x101419 7)
      [] [] [.rip] :=
    (nopEffect_footprint 0x101419 7).toInstrSpec (nop_m_effect_step 0x101419 [] (by decide) (by decide) (.base 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (6, 6), (9, 9), (10, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013e7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (4, 4), (6, 6), (8, 55), (9, 9), (10, 53), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013ef) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (4, 4), (6, 6), (8, 55), (9, 9), (10, 53), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013f4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (2, 59), (4, 4), (6, 6), (8, 55), (9, 9), (10, 53), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1013f8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (2, 59), (4, 4), (6, 6), (8, 55), (9, 9), (10, 53), (11, 61), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101400) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 63), (2, 59), (4, 4), (6, 6), (8, 55), (9, 9), (10, 53), (11, 61), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101404) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (2, 59), (4, 4), (6, 6), (8, 55), (9, 9), (10, 53), (11, 61), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101408) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 65), (2, 59), (3, 67), (4, 4), (6, 6), (8, 55), (9, 9), (10, 53), (11, 61), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101410) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 65), (2, 69), (3, 67), (4, 4), (6, 6), (8, 55), (9, 9), (10, 53), (11, 61), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101413) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 65), (2, 71), (3, 67), (4, 4), (6, 6), (8, 55), (9, 9), (10, 53), (11, 61), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101417) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 65), (2, 71), (3, 67), (4, 4), (6, 73), (8, 55), (9, 9), (10, 53), (11, 61), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101419) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 65), (2, 71), (3, 67), (4, 4), (6, 73), (8, 55), (9, 9), (10, 53), (11, 61), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101420) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 76) (by decide) rfl

theorem block_l1013e3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1013e3 :=
  Rest.liftedBlock (rest_l1013e3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1013e3 x hx)

theorem rest_l101420 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101420 bytes_l101420) (entryMap (live .l101420))
      15 0x101420 bytes_l101420 b_l101420 := by
  have f0 : InstrSpec 0x101420 [0x41, 0x0F, 0xB6, 0x7C, 0x31, 0x40] (LoadPre 0x101420 (fun s => AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x40)) s (0x101420 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101420 6 7 (.sib 9 (some 6) 0 (.d8 0x40)))
      [.gpr 9, .gpr 6] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x101420 6 7 (.sib 9 (some 6) 0 (.d8 0x40))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101420 0x41 (by decide) 7 (.sib 9 (some 6) 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101426 [0x40, 0x32, 0x7C, 0x31, 0xFD] (LoadPre 0x101426 (fun s => AddrMode.addr (.sib 1 (some 6) 0 (.d8 0xfd)) s (0x101426 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x101426 5 7 (.sib 1 (some 6) 0 (.d8 0xfd)))
      [.gpr 7, .gpr 1, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101426 5 7 (.sib 1 (some 6) 0 (.d8 0xfd))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101426 0x40 (by decide) 7 (.sib 1 (some 6) 0 (.d8 0xfd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10142b [0x40, 0x88, 0x7C, 0x32, 0xFD] (StorePre 0x10142b 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0xfd)) s (0x10142b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10142b 5 7 (.sib 2 (some 6) 0 (.d8 0xfd)))
      [.gpr 7, .gpr 2, .gpr 6] [] [.rip] :=
    (movM8R8Effect_footprint 0x10142b 5 7 (.sib 2 (some 6) 0 (.d8 0xfd))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10142b 0x40 (by decide) 7 (.sib 2 (some 6) 0 (.d8 0xfd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x101430 [0x41, 0x0F, 0xB6, 0x7C, 0x31, 0x41] (LoadPre 0x101430 (fun s => AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x41)) s (0x101430 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101430 6 7 (.sib 9 (some 6) 0 (.d8 0x41)))
      [.gpr 9, .gpr 6] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x101430 6 7 (.sib 9 (some 6) 0 (.d8 0x41))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101430 0x41 (by decide) 7 (.sib 9 (some 6) 0 (.d8 0x41)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x101436 [0x40, 0x32, 0x7C, 0x31, 0xFE] (LoadPre 0x101436 (fun s => AddrMode.addr (.sib 1 (some 6) 0 (.d8 0xfe)) s (0x101436 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x101436 5 7 (.sib 1 (some 6) 0 (.d8 0xfe)))
      [.gpr 7, .gpr 1, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101436 5 7 (.sib 1 (some 6) 0 (.d8 0xfe))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101436 0x40 (by decide) 7 (.sib 1 (some 6) 0 (.d8 0xfe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10143b [0x40, 0x88, 0x7C, 0x32, 0xFE] (StorePre 0x10143b 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0xfe)) s (0x10143b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10143b 5 7 (.sib 2 (some 6) 0 (.d8 0xfe)))
      [.gpr 7, .gpr 2, .gpr 6] [] [.rip] :=
    (movM8R8Effect_footprint 0x10143b 5 7 (.sib 2 (some 6) 0 (.d8 0xfe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10143b 0x40 (by decide) 7 (.sib 2 (some 6) 0 (.d8 0xfe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101440 [0x41, 0x0F, 0xB6, 0x7C, 0x31, 0x42] (LoadPre 0x101440 (fun s => AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x42)) s (0x101440 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101440 6 7 (.sib 9 (some 6) 0 (.d8 0x42)))
      [.gpr 9, .gpr 6] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x101440 6 7 (.sib 9 (some 6) 0 (.d8 0x42))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101440 0x41 (by decide) 7 (.sib 9 (some 6) 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x101446 [0x40, 0x32, 0x7C, 0x31, 0xFF] (LoadPre 0x101446 (fun s => AddrMode.addr (.sib 1 (some 6) 0 (.d8 0xff)) s (0x101446 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x101446 5 7 (.sib 1 (some 6) 0 (.d8 0xff)))
      [.gpr 7, .gpr 1, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101446 5 7 (.sib 1 (some 6) 0 (.d8 0xff))).toInstrSpec (xor_r8_m8_rex_effect_step 0x101446 0x40 (by decide) 7 (.sib 1 (some 6) 0 (.d8 0xff)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x10144b [0x40, 0x88, 0x7C, 0x32, 0xFF] (StorePre 0x10144b 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0xff)) s (0x10144b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10144b 5 7 (.sib 2 (some 6) 0 (.d8 0xff)))
      [.gpr 7, .gpr 2, .gpr 6] [] [.rip] :=
    (movM8R8Effect_footprint 0x10144b 5 7 (.sib 2 (some 6) 0 (.d8 0xff))).toInstrSpec (mov_m8_r8_rex_effect_step 0x10144b 0x40 (by decide) 7 (.sib 2 (some 6) 0 (.d8 0xff)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101450 [0x41, 0x0F, 0xB6, 0x7C, 0x31, 0x43] (LoadPre 0x101450 (fun s => AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x43)) s (0x101450 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101450 6 7 (.sib 9 (some 6) 0 (.d8 0x43)))
      [.gpr 9, .gpr 6] [] [.reg 7, .rip] :=
    (movzxR32M8Effect_footprint 0x101450 6 7 (.sib 9 (some 6) 0 (.d8 0x43))).toInstrSpec (movzx_r32_m8_rex_effect_step 0x101450 0x41 (by decide) 7 (.sib 9 (some 6) 0 (.d8 0x43)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101456 [0x40, 0x32, 0x3C, 0x31] (LoadPre 0x101456 (fun s => AddrMode.addr (.sib 1 (some 6) 0 .none) s (0x101456 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101456 4 7 (.sib 1 (some 6) 0 .none))
      [.gpr 7, .gpr 1, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101456 4 7 (.sib 1 (some 6) 0 .none)).toInstrSpec (xor_r8_m8_rex_effect_step 0x101456 0x40 (by decide) 7 (.sib 1 (some 6) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x10145a [0x40, 0x88, 0x3C, 0x32] (StorePre 0x10145a 4 (fun s => AddrMode.addr (.sib 2 (some 6) 0 .none) s (0x10145a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10145a 4 7 (.sib 2 (some 6) 0 .none))
      [.gpr 7, .gpr 2, .gpr 6] [] [.rip] :=
    (movM8R8Effect_footprint 0x10145a 4 7 (.sib 2 (some 6) 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x10145a 0x40 (by decide) 7 (.sib 2 (some 6) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x10145e [0x48, 0x83, 0xC6, 0x04] (fun s => s.RIP = 0x10145e) (addR64Imm8Effect 0x10145e 6 0x4)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10145e 6 0x4).toInstrSpec (add_r64_imm8_effect_step 0x10145e 0x48 0xc6 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x101462 [0x49, 0x39, 0xF2] (fun s => s.RIP = 0x101462) (cmpR64R64Effect 0x101462 10 6)
      [.gpr 10, .gpr 6] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x101462 10 6).toInstrSpec (cmp_r64_r64_effect_step 0x101462 0x49 0xf2 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101426) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10142b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101430) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 58), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101436) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10143b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101440) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101446) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10144b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101450) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101456) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10145a) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10145e) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 73), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101462) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 73), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101465) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 77) (jcc_rel8_effect_step 0x101465 5 0xb9) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101420 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101420 :=
  Rest.liftedBlock (rest_l101420 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101420 x hx)

theorem rest_l101467 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101467 bytes_l101467) (entryMap (live .l101467))
      2 0x101467 bytes_l101467 b_l101467 := by
  have f0 : InstrSpec 0x101467 [0x48, 0x85, 0xC0] (fun s => s.RIP = 0x101467) (testR64R64Effect 0x101467 0 0)
      [.gpr 0, .gpr 0] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x101467 0 0).toInstrSpec (test_r64_r64_effect_step 0x101467 0x48 0xc0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10146a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel8_effect_step 0x10146a 4 0x38) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101467 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101467 :=
  Rest.liftedBlock (rest_l101467 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101467 x hx)

theorem rest_l10146c [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10146c bytes_l10146c) (entryMap (live .l10146c))
      8 0x10146c bytes_l10146c b_l10146c := by
  have f0 : InstrSpec 0x10146c [0x4A, 0x8D, 0x0C, 0x0E] (fun s => s.RIP = 0x10146c) (leaR64Effect 0x10146c 1 (.sib 6 (some 9) 0 .none))
      [.gpr 6, .gpr 9] [] [.reg 1, .rip] :=
    (leaR64Effect_footprint 0x10146c 1 (.sib 6 (some 9) 0 .none)).toInstrSpec (lea_r64_effect_step 0x10146c 0x4a (by decide) 1 (.sib 6 (some 9) 0 .none) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101470 [0x48, 0x83, 0xC1, 0x40] (fun s => s.RIP = 0x101470) (addR64Imm8Effect 0x101470 1 0x40)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x101470 1 0x40).toInstrSpec (add_r64_imm8_effect_step 0x101470 0x48 0xc1 0x40 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101474 [0x49, 0x01, 0xF0] (fun s => s.RIP = 0x101474) (addR64R64Effect 0x101474 8 6)
      [.gpr 8, .gpr 6] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101474 8 6).toInstrSpec (add_r64_r64_effect_step 0x101474 0x49 0xf0 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101477 [0x4D, 0x01, 0xF8] (fun s => s.RIP = 0x101477) (addR64R64Effect 0x101477 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (addR64R64Effect_footprint 0x101477 8 15).toInstrSpec (add_r64_r64_effect_step 0x101477 0x4d 0xf8 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10147a [0x4C, 0x01, 0xC3] (fun s => s.RIP = 0x10147a) (addR64R64Effect 0x10147a 3 8)
      [.gpr 3, .gpr 8] [] [.reg 3, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10147a 3 8).toInstrSpec (add_r64_r64_effect_step 0x10147a 0x4c 0xc3 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10147d [0x4D, 0x01, 0xC3] (fun s => s.RIP = 0x10147d) (addR64R64Effect 0x10147d 11 8)
      [.gpr 11, .gpr 8] [] [.reg 11, .flags, .rip] :=
    (addR64R64Effect_footprint 0x10147d 11 8).toInstrSpec (add_r64_r64_effect_step 0x10147d 0x4d 0xc3 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101480 [0x31, 0xD2] (fun s => s.RIP = 0x101480) (xorR32R32Effect 0x101480 2 2 2)
      [.gpr 2, .gpr 2] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101480 2 2 2).toInstrSpec (xor_r32_r32_effect_step 0x101480 0xd2 (by decide)) pre_rip
  have f7 : InstrSpec 0x101482 [0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101482) (fun _ => nopEffect 0x101482 14)
      [] [] [.rip] :=
    (nopEffect_footprint 0x101482 14).toInstrSpec (nop_m_effect_step 0x101482 [0x66, 0x66, 0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101470) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101474) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101477) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10147a) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 61), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (11, 11), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10147d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 55), (2, 2), (3, 61), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (11, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101480) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 55), (2, 65), (3, 61), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (11, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101482) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 55), (2, 65), (3, 61), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (11, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101490) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 68) (by decide) rfl

theorem block_l10146c [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10146c :=
  Rest.liftedBlock (rest_l10146c code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10146c x hx)

theorem rest_l101490 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101490 bytes_l101490) (entryMap (live .l101490))
      6 0x101490 bytes_l101490 b_l101490 := by
  have f0 : InstrSpec 0x101490 [0x0F, 0xB6, 0x34, 0x11] (LoadPre 0x101490 (fun s => AddrMode.addr (.sib 1 (some 2) 0 .none) s (0x101490 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x101490 4 6 (.sib 1 (some 2) 0 .none))
      [.gpr 1, .gpr 2] [] [.reg 6, .rip] :=
    (movzxR32M8Effect_footprint 0x101490 4 6 (.sib 1 (some 2) 0 .none)).toInstrSpec (movzx_r32_m8_effect_step 0x101490 6 (.sib 1 (some 2) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x101494 [0x41, 0x32, 0x34, 0x13] (LoadPre 0x101494 (fun s => AddrMode.addr (.sib 11 (some 2) 0 .none) s (0x101494 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101494 4 6 (.sib 11 (some 2) 0 .none))
      [.gpr 6, .gpr 11, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR8M8Effect_footprint 0x101494 4 6 (.sib 11 (some 2) 0 .none)).toInstrSpec (xor_r8_m8_rex_effect_step 0x101494 0x41 (by decide) 6 (.sib 11 (some 2) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x101498 [0x40, 0x88, 0x34, 0x13] (StorePre 0x101498 4 (fun s => AddrMode.addr (.sib 3 (some 2) 0 .none) s (0x101498 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101498 4 6 (.sib 3 (some 2) 0 .none))
      [.gpr 6, .gpr 3, .gpr 2] [] [.rip] :=
    (movM8R8Effect_footprint 0x101498 4 6 (.sib 3 (some 2) 0 .none)).toInstrSpec (mov_m8_r8_rex_effect_step 0x101498 0x40 (by decide) 6 (.sib 3 (some 2) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10149c [0x48, 0xFF, 0xC2] (fun s => s.RIP = 0x10149c) (incR64Effect 0x10149c 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (incR64Effect_footprint 0x10149c 2).toInstrSpec (inc_r64_effect_step 0x10149c 0x48 0xc2 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10149f [0x48, 0x39, 0xD0] (fun s => s.RIP = 0x10149f) (cmpR64R64Effect 0x10149f 0 2)
      [.gpr 0, .gpr 2] [] [.flags, .rip] :=
    (cmpR64R64Effect_footprint 0x10149f 0 2).toInstrSpec (cmp_r64_r64_effect_step 0x10149f 0x48 0xd0 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 53), (7, 7), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101494) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 7), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101498) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 7), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10149c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (6, 55), (7, 7), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10149f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (6, 55), (7, 7), (9, 9), (11, 11), (14, 14), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014a2) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 62) (jcc_rel8_effect_step 0x1014a2 5 0xec) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l101490 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101490 :=
  Rest.liftedBlock (rest_l101490 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101490 x hx)

theorem rest_l1014a4 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014a4 bytes_l1014a4) (entryMap (live .l1014a4))
      1 0x1014a4 bytes_l1014a4 b_l1014a4 := by
  have f0 : InstrSpec 0x1014a4 [0x45, 0x88, 0x71, 0x40] (StorePre 0x1014a4 4 (fun s => AddrMode.addr (.base 9 (.d8 0x40)) s (0x1014a4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1014a4 4 14 (.base 9 (.d8 0x40)))
      [.gpr 14, .gpr 9] [] [.rip] :=
    (movM8R8Effect_footprint 0x1014a4 4 14 (.base 9 (.d8 0x40))).toInstrSpec (mov_m8_r8_rex_effect_step 0x1014a4 0x45 (by decide) 6 (.base 9 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014a8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 54) (by decide) rfl

theorem block_l1014a4 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014a4 :=
  Rest.liftedBlock (rest_l1014a4 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014a4 x hx)

theorem rest_l1014a8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014a8 bytes_l1014a8) (entryMap (live .l1014a8))
      1 0x1014a8 bytes_l1014a8 b_l1014a8 := by
  have f0 : InstrSpec 0x1014a8 [0x31, 0xC0] (fun s => s.RIP = 0x1014a8) (xorR32R32Effect 0x1014a8 2 0 0)
      [.gpr 0, .gpr 0] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1014a8 2 0 0).toInstrSpec (xor_r32_r32_effect_step 0x1014a8 0xc0 (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014aa) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l1014a8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014a8 :=
  Rest.liftedBlock (rest_l1014a8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014a8 x hx)

theorem rest_l1014aa [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1014aa bytes_l1014aa) (entryMap (live .l1014aa))
      8 0x1014aa bytes_l1014aa b_l1014aa := by
  have f0 : InstrSpec 0x1014aa [0x48, 0x81, 0xC4, 0x70, 0x01, 0x00, 0x00] (fun s => s.RIP = 0x1014aa) (addR64Imm32Effect 0x1014aa 4 0x170)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x1014aa 4 0x170).toInstrSpec (add_r64_imm32_effect_step 0x1014aa 0x48 0xc4 0x170 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1014b1 [0x5B] (PopPre 0x1014b1) (popR64Effect 0x1014b1 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1014b1 1 3).toInstrSpec (pop_r64_effect_step 0x1014b1 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x1014b2 [0x41, 0x5C] (PopPre 0x1014b2) (popR64Effect 0x1014b2 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1014b2 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1014b2 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1014b4 [0x41, 0x5D] (PopPre 0x1014b4) (popR64Effect 0x1014b4 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1014b4 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1014b4 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1014b6 [0x41, 0x5E] (PopPre 0x1014b6) (popR64Effect 0x1014b6 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1014b6 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1014b6 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1014b8 [0x41, 0x5F] (PopPre 0x1014b8) (popR64Effect 0x1014b8 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1014b8 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1014b8 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1014ba [0x5D] (PopPre 0x1014ba) (popR64Effect 0x1014ba 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1014ba 1 5).toInstrSpec (pop_r64_effect_step 0x1014ba 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1014bb [0xC3] (RetPre 0x1014bb) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1014bb).toInstrSpec (ret_effect_step 0x1014bb) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 53), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 56), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014b2) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f2 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 59) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (6, 6), (7, 7), (9, 9), (12, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014b4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 62) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014b6) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 65) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 65), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014b8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 68) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 68), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014ba) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f6 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 71), (5, 70), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1014bb) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f7 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 74) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)]) f7 (by decide) rfl rfl rfl (by decide)

theorem block_l1014aa [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1014aa :=
  Rest.liftedBlock (rest_l1014aa code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1014aa x hx)

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

theorem_by block_l1012b0_eval :
    program.runBlock (dialect code) ⟨.l1012b0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1012d8_eval :
    program.runBlock (dialect code) ⟨.l1012d8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1012e3_eval :
    program.runBlock (dialect code) ⟨.l1012e3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10133c_eval :
    program.runBlock (dialect code) ⟨.l10133c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101386_eval :
    program.runBlock (dialect code) ⟨.l101386, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1013bf_eval :
    program.runBlock (dialect code) ⟨.l1013bf, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1013e3_eval :
    program.runBlock (dialect code) ⟨.l1013e3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101420_eval :
    program.runBlock (dialect code) ⟨.l101420, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101467_eval :
    program.runBlock (dialect code) ⟨.l101467, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10146c_eval :
    program.runBlock (dialect code) ⟨.l10146c, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101490_eval :
    program.runBlock (dialect code) ⟨.l101490, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014a4_eval :
    program.runBlock (dialect code) ⟨.l1014a4, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014a8_eval :
    program.runBlock (dialect code) ⟨.l1014a8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1014aa_eval :
    program.runBlock (dialect code) ⟨.l1014aa, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
