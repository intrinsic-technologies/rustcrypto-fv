import K256.Proofs.Ecdh.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Ecdh.LIR.Generated.Values

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

theorem rest_l11aa40_5 [Bindings] (code : CodeMap) :
    Rest (n := 226) code lifted (codeRange 0x11aa40 bytes_l11aa40) [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 220), (7, 224), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      17 0x11abb6 bytes_l11aa40_5 b_l11aa40_5 := by
  have f100 : InstrSpec 0x11abb6 [0x40, 0x88, 0x7C, 0x24, 0x1A] (StorePre 0x11abb6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x11abb6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11abb6 5 7 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11abb6 5 7 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11abb6 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f101 : InstrSpec 0x11abbb [0x40, 0xC0, 0xEE, 0x04] (fun s => s.RIP = 0x11abbb) (shrR8Effect 0x11abbb 4 6 4)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR8Effect_footprint 0x11abbb 4 6 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11abbb 0x40 0xee 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f102 : InstrSpec 0x11abbf [0x40, 0x88, 0x74, 0x24, 0x1B] (StorePre 0x11abbf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x11abbf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11abbf 5 6 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11abbf 5 6 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11abbf 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f103 : InstrSpec 0x11abc4 [0x89, 0xD6] (fun s => s.RIP = 0x11abc4) (movR32R32Effect 0x11abc4 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x11abc4 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x11abc4 0xd6 (by decide)) pre_rip
  have f104 : InstrSpec 0x11abc6 [0xC1, 0xEE, 0x08] (fun s => s.RIP = 0x11abc6) (shrR32Effect 0x11abc6 3 6 8)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x11abc6 3 6 8).toInstrSpec (shr_r32_imm8_effect_step 0x11abc6 0xee 0x8 (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x11abc9 [0x89, 0xF7] (fun s => s.RIP = 0x11abc9) (movR32R32Effect 0x11abc9 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11abc9 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11abc9 0xf7 (by decide)) pre_rip
  have f106 : InstrSpec 0x11abcb [0x40, 0x80, 0xE7, 0x0F] (fun s => s.RIP = 0x11abcb) (andR8Imm8Effect 0x11abcb 4 7 0xf)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11abcb 4 7 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11abcb 0x40 0xe7 0xf (by decide) (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x11abcf [0x40, 0x88, 0x7C, 0x24, 0x1C] (StorePre 0x11abcf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x11abcf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11abcf 5 7 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11abcf 5 7 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11abcf 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f108 : InstrSpec 0x11abd4 [0x40, 0xC0, 0xEE, 0x04] (fun s => s.RIP = 0x11abd4) (shrR8Effect 0x11abd4 4 6 4)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR8Effect_footprint 0x11abd4 4 6 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11abd4 0x40 0xee 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f109 : InstrSpec 0x11abd8 [0x40, 0x88, 0x74, 0x24, 0x1D] (StorePre 0x11abd8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x11abd8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11abd8 5 6 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11abd8 5 6 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11abd8 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f110 : InstrSpec 0x11abdd [0x89, 0xD6] (fun s => s.RIP = 0x11abdd) (movR32R32Effect 0x11abdd 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x11abdd 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x11abdd 0xd6 (by decide)) pre_rip
  have f111 : InstrSpec 0x11abdf [0x40, 0x80, 0xE6, 0x0F] (fun s => s.RIP = 0x11abdf) (andR8Imm8Effect 0x11abdf 4 6 0xf)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11abdf 4 6 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11abdf 0x40 0xe6 0xf (by decide) (by decide) (by decide)) pre_rip
  have f112 : InstrSpec 0x11abe3 [0x40, 0x88, 0x74, 0x24, 0x1E] (StorePre 0x11abe3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x11abe3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11abe3 5 6 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11abe3 5 6 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11abe3 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f113 : InstrSpec 0x11abe8 [0xC0, 0xEA, 0x04] (fun s => s.RIP = 0x11abe8) (shrR8Effect 0x11abe8 3 2 4)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR8Effect_footprint 0x11abe8 3 2 4).toInstrSpec (shr_r8_imm8_effect_step 0x11abe8 0xea 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f114 : InstrSpec 0x11abeb [0x88, 0x54, 0x24, 0x1F] (StorePre 0x11abeb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x11abeb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11abeb 4 2 (.sib 4 none 0 (.d8 0x1f)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11abeb 4 2 (.sib 4 none 0 (.d8 0x1f))).toInstrSpec (mov_m8_r8_effect_step 0x11abeb 2 (by decide) (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f115 : InstrSpec 0x11abef [0xBA, 0x02, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11abef) (movR32Imm32Effect 0x11abef 5 2 0x2)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x11abef 5 2 0x2).toInstrSpec (mov_r32_imm32_effect_step 0x11abef 0xba (by decide) 0x2) pre_rip
  have f116 : InstrSpec 0x11abf4 [0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x11abf4) (fun _ => nopEffect 0x11abf4 12)
      [] [] [.rip] :=
    (nopEffect_footprint 0x11abf4 12).toInstrSpec (nop_m_effect_step 0x11abf4 [0x66, 0x66, 0x66, 0x2E] (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 226) (RestInside.exec (n := 226) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 220), (7, 224), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abbb) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f101 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 227), (7, 224), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abbf) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.exec (n := 229) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 227), (7, 224), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abc4) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f103 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 230), (7, 224), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abc6) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f104 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 232), (7, 224), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abc9) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f105 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 232), (7, 234), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abcb) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f106 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 232), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abcf) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.exec (n := 238) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 232), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abd4) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 239) (RestInside.out (n := 239) f108 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 240) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 239), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abd8) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 241) (RestInside.exec (n := 241) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 239), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abdd) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f110 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 242), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abdf) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f111 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 244), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abe3) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 246) (RestInside.exec (n := 246) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 244), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abe8) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f113 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 55), (1, 70), (2, 247), (3, 3), (4, 53), (5, 5), (6, 244), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abeb) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.exec (n := 249) (ρ' := [(0, 55), (1, 70), (2, 247), (3, 3), (4, 53), (5, 5), (6, 244), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abef) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f115 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 55), (1, 70), (2, 250), (3, 3), (4, 53), (5, 5), (6, 244), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abf4) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.exec (n := 252) (ρ' := [(0, 55), (1, 70), (2, 250), (3, 3), (4, 53), (5, 5), (6, 244), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac00) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 253) (by decide) rfl

theorem rest_l11aa40_4 [Bindings] (code : CodeMap) :
    Rest (n := 191) code lifted (codeRange 0x11aa40 bytes_l11aa40) [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 184), (7, 188), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      37 0x11ab6f bytes_l11aa40_4 b_l11aa40_4 := by
  have f80 : InstrSpec 0x11ab6f [0x40, 0xC0, 0xEE, 0x04] (fun s => s.RIP = 0x11ab6f) (shrR8Effect 0x11ab6f 4 6 4)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR8Effect_footprint 0x11ab6f 4 6 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11ab6f 0x40 0xee 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f81 : InstrSpec 0x11ab73 [0x40, 0x88, 0x74, 0x24, 0x15] (StorePre 0x11ab73 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x11ab73 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab73 5 6 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab73 5 6 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab73 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f82 : InstrSpec 0x11ab78 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x11ab78) (movR64R64Effect 0x11ab78 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11ab78 6 2).toInstrSpec (mov_r64_r64_effect_step 0x11ab78 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x11ab7b [0x48, 0xC1, 0xEE, 0x20] (fun s => s.RIP = 0x11ab7b) (shrR64Effect 0x11ab7b 4 6 32)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11ab7b 4 6 32).toInstrSpec (shr_r64_imm8_effect_step 0x11ab7b 0x48 0xee 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f84 : InstrSpec 0x11ab7f [0x89, 0xF7] (fun s => s.RIP = 0x11ab7f) (movR32R32Effect 0x11ab7f 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11ab7f 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11ab7f 0xf7 (by decide)) pre_rip
  have f85 : InstrSpec 0x11ab81 [0x40, 0x80, 0xE7, 0x0F] (fun s => s.RIP = 0x11ab81) (andR8Imm8Effect 0x11ab81 4 7 0xf)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11ab81 4 7 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11ab81 0x40 0xe7 0xf (by decide) (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x11ab85 [0x40, 0x88, 0x7C, 0x24, 0x16] (StorePre 0x11ab85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x11ab85 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab85 5 7 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab85 5 7 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab85 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f87 : InstrSpec 0x11ab8a [0x40, 0xC0, 0xEE, 0x04] (fun s => s.RIP = 0x11ab8a) (shrR8Effect 0x11ab8a 4 6 4)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR8Effect_footprint 0x11ab8a 4 6 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11ab8a 0x40 0xee 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x11ab8e [0x40, 0x88, 0x74, 0x24, 0x17] (StorePre 0x11ab8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x11ab8e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab8e 5 6 (.sib 4 none 0 (.d8 0x17)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab8e 5 6 (.sib 4 none 0 (.d8 0x17))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab8e 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f89 : InstrSpec 0x11ab93 [0x89, 0xD6] (fun s => s.RIP = 0x11ab93) (movR32R32Effect 0x11ab93 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x11ab93 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x11ab93 0xd6 (by decide)) pre_rip
  have f90 : InstrSpec 0x11ab95 [0xC1, 0xEE, 0x18] (fun s => s.RIP = 0x11ab95) (shrR32Effect 0x11ab95 3 6 24)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x11ab95 3 6 24).toInstrSpec (shr_r32_imm8_effect_step 0x11ab95 0xee 0x18 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x11ab98 [0x40, 0x80, 0xE6, 0x0F] (fun s => s.RIP = 0x11ab98) (andR8Imm8Effect 0x11ab98 4 6 0xf)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11ab98 4 6 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11ab98 0x40 0xe6 0xf (by decide) (by decide) (by decide)) pre_rip
  have f92 : InstrSpec 0x11ab9c [0x40, 0x88, 0x74, 0x24, 0x18] (StorePre 0x11ab9c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ab9c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab9c 5 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab9c 5 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab9c 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f93 : InstrSpec 0x11aba1 [0x89, 0xD6] (fun s => s.RIP = 0x11aba1) (movR32R32Effect 0x11aba1 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x11aba1 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x11aba1 0xd6 (by decide)) pre_rip
  have f94 : InstrSpec 0x11aba3 [0xC1, 0xEE, 0x1C] (fun s => s.RIP = 0x11aba3) (shrR32Effect 0x11aba3 3 6 28)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x11aba3 3 6 28).toInstrSpec (shr_r32_imm8_effect_step 0x11aba3 0xee 0x1c (by decide) (by decide)) pre_rip
  have f95 : InstrSpec 0x11aba6 [0x40, 0x88, 0x74, 0x24, 0x19] (StorePre 0x11aba6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x11aba6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aba6 5 6 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aba6 5 6 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aba6 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f96 : InstrSpec 0x11abab [0x89, 0xD6] (fun s => s.RIP = 0x11abab) (movR32R32Effect 0x11abab 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x11abab 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x11abab 0xd6 (by decide)) pre_rip
  have f97 : InstrSpec 0x11abad [0xC1, 0xEE, 0x10] (fun s => s.RIP = 0x11abad) (shrR32Effect 0x11abad 3 6 16)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x11abad 3 6 16).toInstrSpec (shr_r32_imm8_effect_step 0x11abad 0xee 0x10 (by decide) (by decide)) pre_rip
  have f98 : InstrSpec 0x11abb0 [0x89, 0xF7] (fun s => s.RIP = 0x11abb0) (movR32R32Effect 0x11abb0 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11abb0 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11abb0 0xf7 (by decide)) pre_rip
  have f99 : InstrSpec 0x11abb2 [0x40, 0x80, 0xE7, 0x0F] (fun s => s.RIP = 0x11abb2) (andR8Imm8Effect 0x11abb2 4 7 0xf)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11abb2 4 7 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11abb2 0x40 0xe7 0xf (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f80 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 191), (7, 188), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab73) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.exec (n := 193) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 191), (7, 188), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab78) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 194) (RestInside.out (n := 194) f82 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 195) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 194), (7, 188), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab7b) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 196) (RestInside.out (n := 196) f83 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 197) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 196), (7, 188), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab7f) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 198) (RestInside.out (n := 198) f84 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 199) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 196), (7, 198), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab81) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f85 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 196), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab85) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.exec (n := 202) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 196), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab8a) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f87 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 203), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab8e) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.exec (n := 205) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 203), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab93) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f89 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 206), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab95) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f90 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 208), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab98) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f91 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 210), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab9c) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.exec (n := 212) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 210), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aba1) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f93 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 214) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 213), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aba3) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f94 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 215), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aba6) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.exec (n := 217) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 215), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abab) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f96 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 218), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abad) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.out (n := 220) f97 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 221) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 220), (7, 200), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abb0) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 222) (RestInside.out (n := 222) f98 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 223) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 220), (7, 222), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abb2) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 224) (RestInside.out (n := 224) f99 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 225) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 220), (7, 224), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11abb6) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11aa40_5 code

theorem rest_l11aa40_3 [Bindings] (code : CodeMap) :
    Rest (n := 157) code lifted (codeRange 0x11aa40 bytes_l11aa40) [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 155), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      57 0x11ab21 bytes_l11aa40_3 b_l11aa40_3 := by
  have f60 : InstrSpec 0x11ab21 [0x40, 0x88, 0x74, 0x24, 0x0F] (StorePre 0x11ab21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x11ab21 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab21 5 6 (.sib 4 none 0 (.d8 0xf)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab21 5 6 (.sib 4 none 0 (.d8 0xf))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab21 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f61 : InstrSpec 0x11ab26 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x11ab26) (movR64R64Effect 0x11ab26 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11ab26 6 2).toInstrSpec (mov_r64_r64_effect_step 0x11ab26 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x11ab29 [0x48, 0xC1, 0xEE, 0x38] (fun s => s.RIP = 0x11ab29) (shrR64Effect 0x11ab29 4 6 56)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11ab29 4 6 56).toInstrSpec (shr_r64_imm8_effect_step 0x11ab29 0x48 0xee 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x11ab2d [0x40, 0x80, 0xE6, 0x0F] (fun s => s.RIP = 0x11ab2d) (andR8Imm8Effect 0x11ab2d 4 6 0xf)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11ab2d 4 6 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11ab2d 0x40 0xe6 0xf (by decide) (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x11ab31 [0x40, 0x88, 0x74, 0x24, 0x10] (StorePre 0x11ab31 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ab31 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab31 5 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab31 5 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab31 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f65 : InstrSpec 0x11ab36 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x11ab36) (movR64R64Effect 0x11ab36 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11ab36 6 2).toInstrSpec (mov_r64_r64_effect_step 0x11ab36 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x11ab39 [0x48, 0xC1, 0xEE, 0x3C] (fun s => s.RIP = 0x11ab39) (shrR64Effect 0x11ab39 4 6 60)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11ab39 4 6 60).toInstrSpec (shr_r64_imm8_effect_step 0x11ab39 0x48 0xee 0x3c (by decide) (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x11ab3d [0x40, 0x88, 0x74, 0x24, 0x11] (StorePre 0x11ab3d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x11ab3d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab3d 5 6 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab3d 5 6 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab3d 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f68 : InstrSpec 0x11ab42 [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x11ab42) (movR64R64Effect 0x11ab42 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11ab42 6 2).toInstrSpec (mov_r64_r64_effect_step 0x11ab42 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x11ab45 [0x48, 0xC1, 0xEE, 0x30] (fun s => s.RIP = 0x11ab45) (shrR64Effect 0x11ab45 4 6 48)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11ab45 4 6 48).toInstrSpec (shr_r64_imm8_effect_step 0x11ab45 0x48 0xee 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x11ab49 [0x89, 0xF7] (fun s => s.RIP = 0x11ab49) (movR32R32Effect 0x11ab49 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11ab49 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11ab49 0xf7 (by decide)) pre_rip
  have f71 : InstrSpec 0x11ab4b [0x40, 0x80, 0xE7, 0x0F] (fun s => s.RIP = 0x11ab4b) (andR8Imm8Effect 0x11ab4b 4 7 0xf)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11ab4b 4 7 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11ab4b 0x40 0xe7 0xf (by decide) (by decide) (by decide)) pre_rip
  have f72 : InstrSpec 0x11ab4f [0x40, 0x88, 0x7C, 0x24, 0x12] (StorePre 0x11ab4f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x11ab4f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab4f 5 7 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab4f 5 7 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab4f 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f73 : InstrSpec 0x11ab54 [0x40, 0xC0, 0xEE, 0x04] (fun s => s.RIP = 0x11ab54) (shrR8Effect 0x11ab54 4 6 4)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR8Effect_footprint 0x11ab54 4 6 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11ab54 0x40 0xee 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x11ab58 [0x40, 0x88, 0x74, 0x24, 0x13] (StorePre 0x11ab58 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x11ab58 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab58 5 6 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab58 5 6 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab58 0x40 (by decide) 6 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f75 : InstrSpec 0x11ab5d [0x48, 0x89, 0xD6] (fun s => s.RIP = 0x11ab5d) (movR64R64Effect 0x11ab5d 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x11ab5d 6 2).toInstrSpec (mov_r64_r64_effect_step 0x11ab5d 0x48 0xd6 (by decide) (by decide)) pre_rip
  have f76 : InstrSpec 0x11ab60 [0x48, 0xC1, 0xEE, 0x28] (fun s => s.RIP = 0x11ab60) (shrR64Effect 0x11ab60 4 6 40)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR64Effect_footprint 0x11ab60 4 6 40).toInstrSpec (shr_r64_imm8_effect_step 0x11ab60 0x48 0xee 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x11ab64 [0x89, 0xF7] (fun s => s.RIP = 0x11ab64) (movR32R32Effect 0x11ab64 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11ab64 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11ab64 0xf7 (by decide)) pre_rip
  have f78 : InstrSpec 0x11ab66 [0x40, 0x80, 0xE7, 0x0F] (fun s => s.RIP = 0x11ab66) (andR8Imm8Effect 0x11ab66 4 7 0xf)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11ab66 4 7 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11ab66 0x40 0xe7 0xf (by decide) (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x11ab6a [0x40, 0x88, 0x7C, 0x24, 0x14] (StorePre 0x11ab6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x11ab6a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab6a 5 7 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab6a 5 7 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab6a 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 157) (RestInside.exec (n := 157) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 155), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab26) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f61 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 158), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab29) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f62 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 160), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab2d) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f63 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 162), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab31) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.exec (n := 164) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 162), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab36) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f65 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 165), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab39) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f66 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 167), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab3d) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 169) (RestInside.exec (n := 169) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 167), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab42) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f68 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 170), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab45) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f69 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 172), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab49) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f70 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 172), (7, 174), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab4b) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f71 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 172), (7, 176), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab4f) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.exec (n := 178) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 172), (7, 176), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab54) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f73 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 179), (7, 176), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab58) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.exec (n := 181) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 179), (7, 176), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab5d) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f75 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 182), (7, 176), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab60) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f76 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 184), (7, 176), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab64) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f77 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 184), (7, 186), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab66) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f78 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 184), (7, 188), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab6a) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.exec (n := 190) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 184), (7, 188), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab6f) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l11aa40_4 code

theorem rest_l11aa40_2 [Bindings] (code : CodeMap) :
    Rest (n := 123) code lifted (codeRange 0x11aa40 bytes_l11aa40) [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 121), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      77 0x11aad6 bytes_l11aa40_2 b_l11aa40_2 := by
  have f40 : InstrSpec 0x11aad6 [0xC1, 0xEF, 0x1C] (fun s => s.RIP = 0x11aad6) (shrR32Effect 0x11aad6 3 7 28)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x11aad6 3 7 28).toInstrSpec (shr_r32_imm8_effect_step 0x11aad6 0xef 0x1c (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x11aad9 [0x40, 0x88, 0x7C, 0x24, 0x09] (StorePre 0x11aad9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x11aad9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aad9 5 7 (.sib 4 none 0 (.d8 0x9)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aad9 5 7 (.sib 4 none 0 (.d8 0x9))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aad9 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f42 : InstrSpec 0x11aade [0x89, 0xF7] (fun s => s.RIP = 0x11aade) (movR32R32Effect 0x11aade 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11aade 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11aade 0xf7 (by decide)) pre_rip
  have f43 : InstrSpec 0x11aae0 [0xC1, 0xEF, 0x10] (fun s => s.RIP = 0x11aae0) (shrR32Effect 0x11aae0 3 7 16)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x11aae0 3 7 16).toInstrSpec (shr_r32_imm8_effect_step 0x11aae0 0xef 0x10 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x11aae3 [0x41, 0x89, 0xF8] (fun s => s.RIP = 0x11aae3) (movR32R32Effect 0x11aae3 3 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x11aae3 3 8 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x11aae3 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x11aae6 [0x41, 0x80, 0xE0, 0x0F] (fun s => s.RIP = 0x11aae6) (andR8Imm8Effect 0x11aae6 4 8 0xf)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11aae6 4 8 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11aae6 0x41 0xe0 0xf (by decide) (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x11aaea [0x44, 0x88, 0x44, 0x24, 0x0A] (StorePre 0x11aaea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x11aaea + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aaea 5 8 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aaea 5 8 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aaea 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f47 : InstrSpec 0x11aaef [0x40, 0xC0, 0xEF, 0x04] (fun s => s.RIP = 0x11aaef) (shrR8Effect 0x11aaef 4 7 4)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR8Effect_footprint 0x11aaef 4 7 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11aaef 0x40 0xef 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x11aaf3 [0x40, 0x88, 0x7C, 0x24, 0x0B] (StorePre 0x11aaf3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x11aaf3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aaf3 5 7 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aaf3 5 7 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aaf3 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x11aaf8 [0x89, 0xF7] (fun s => s.RIP = 0x11aaf8) (movR32R32Effect 0x11aaf8 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11aaf8 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11aaf8 0xf7 (by decide)) pre_rip
  have f50 : InstrSpec 0x11aafa [0xC1, 0xEF, 0x08] (fun s => s.RIP = 0x11aafa) (shrR32Effect 0x11aafa 3 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x11aafa 3 7 8).toInstrSpec (shr_r32_imm8_effect_step 0x11aafa 0xef 0x8 (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x11aafd [0x41, 0x89, 0xF8] (fun s => s.RIP = 0x11aafd) (movR32R32Effect 0x11aafd 3 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x11aafd 3 8 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x11aafd 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x11ab00 [0x41, 0x80, 0xE0, 0x0F] (fun s => s.RIP = 0x11ab00) (andR8Imm8Effect 0x11ab00 4 8 0xf)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11ab00 4 8 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11ab00 0x41 0xe0 0xf (by decide) (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x11ab04 [0x44, 0x88, 0x44, 0x24, 0x0C] (StorePre 0x11ab04 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x11ab04 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab04 5 8 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab04 5 8 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab04 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x11ab09 [0x40, 0xC0, 0xEF, 0x04] (fun s => s.RIP = 0x11ab09) (shrR8Effect 0x11ab09 4 7 4)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR8Effect_footprint 0x11ab09 4 7 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11ab09 0x40 0xef 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x11ab0d [0x40, 0x88, 0x7C, 0x24, 0x0D] (StorePre 0x11ab0d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x11ab0d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab0d 5 7 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab0d 5 7 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab0d 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x11ab12 [0x89, 0xF7] (fun s => s.RIP = 0x11ab12) (movR32R32Effect 0x11ab12 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11ab12 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11ab12 0xf7 (by decide)) pre_rip
  have f57 : InstrSpec 0x11ab14 [0x40, 0x80, 0xE7, 0x0F] (fun s => s.RIP = 0x11ab14) (andR8Imm8Effect 0x11ab14 4 7 0xf)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11ab14 4 7 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11ab14 0x40 0xe7 0xf (by decide) (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x11ab18 [0x40, 0x88, 0x7C, 0x24, 0x0E] (StorePre 0x11ab18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x11ab18 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab18 5 7 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ab18 5 7 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ab18 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f59 : InstrSpec 0x11ab1d [0x40, 0xC0, 0xEE, 0x04] (fun s => s.RIP = 0x11ab1d) (shrR8Effect 0x11ab1d 4 6 4)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR8Effect_footprint 0x11ab1d 4 6 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11ab1d 0x40 0xee 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f40 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 123), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aad9) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 123), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aade) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f42 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 126), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aae0) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f43 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 128), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aae3) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f44 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 128), (8, 130), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aae6) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f45 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 128), (8, 132), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aaea) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.exec (n := 134) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 128), (8, 132), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aaef) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f47 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 135), (8, 132), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aaf3) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 135), (8, 132), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aaf8) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f49 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 138), (8, 132), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aafa) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f50 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 140), (8, 132), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aafd) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.out (n := 142) f51 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 143) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 140), (8, 142), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab00) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 144) (RestInside.out (n := 144) f52 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 145) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 140), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab04) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 146) (RestInside.exec (n := 146) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 140), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab09) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f54 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 147), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab0d) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.exec (n := 149) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 147), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab12) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f56 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 150), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab14) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f57 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab18) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.exec (n := 154) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab1d) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f59 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 155), (7, 152), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ab21) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11aa40_3 code

theorem rest_l11aa40_1 [Bindings] (code : CodeMap) :
    Rest (n := 89) code lifted (codeRange 0x11aa40 bytes_l11aa40) [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 87), (8, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      97 0x11aa89 bytes_l11aa40_1 b_l11aa40_1 := by
  have f20 : InstrSpec 0x11aa89 [0x40, 0x88, 0x7C, 0x24, 0x03] (StorePre 0x11aa89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x11aa89 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aa89 5 7 (.sib 4 none 0 (.d8 0x3)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aa89 5 7 (.sib 4 none 0 (.d8 0x3))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aa89 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x3)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x11aa8e [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x11aa8e) (movR64R64Effect 0x11aa8e 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11aa8e 7 6).toInstrSpec (mov_r64_r64_effect_step 0x11aa8e 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x11aa91 [0x48, 0xC1, 0xEF, 0x28] (fun s => s.RIP = 0x11aa91) (shrR64Effect 0x11aa91 4 7 40)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x11aa91 4 7 40).toInstrSpec (shr_r64_imm8_effect_step 0x11aa91 0x48 0xef 0x28 (by decide) (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x11aa95 [0x41, 0x89, 0xF8] (fun s => s.RIP = 0x11aa95) (movR32R32Effect 0x11aa95 3 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x11aa95 3 8 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x11aa95 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f24 : InstrSpec 0x11aa98 [0x41, 0x80, 0xE0, 0x0F] (fun s => s.RIP = 0x11aa98) (andR8Imm8Effect 0x11aa98 4 8 0xf)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11aa98 4 8 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11aa98 0x41 0xe0 0xf (by decide) (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x11aa9c [0x44, 0x88, 0x44, 0x24, 0x04] (StorePre 0x11aa9c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x11aa9c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aa9c 5 8 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aa9c 5 8 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aa9c 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f26 : InstrSpec 0x11aaa1 [0x40, 0xC0, 0xEF, 0x04] (fun s => s.RIP = 0x11aaa1) (shrR8Effect 0x11aaa1 4 7 4)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR8Effect_footprint 0x11aaa1 4 7 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11aaa1 0x40 0xef 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x11aaa5 [0x40, 0x88, 0x7C, 0x24, 0x05] (StorePre 0x11aaa5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5)) s (0x11aaa5 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aaa5 5 7 (.sib 4 none 0 (.d8 0x5)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aaa5 5 7 (.sib 4 none 0 (.d8 0x5))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aaa5 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x5)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f28 : InstrSpec 0x11aaaa [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x11aaaa) (movR64R64Effect 0x11aaaa 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11aaaa 7 6).toInstrSpec (mov_r64_r64_effect_step 0x11aaaa 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x11aaad [0x48, 0xC1, 0xEF, 0x20] (fun s => s.RIP = 0x11aaad) (shrR64Effect 0x11aaad 4 7 32)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x11aaad 4 7 32).toInstrSpec (shr_r64_imm8_effect_step 0x11aaad 0x48 0xef 0x20 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x11aab1 [0x41, 0x89, 0xF8] (fun s => s.RIP = 0x11aab1) (movR32R32Effect 0x11aab1 3 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x11aab1 3 8 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x11aab1 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x11aab4 [0x41, 0x80, 0xE0, 0x0F] (fun s => s.RIP = 0x11aab4) (andR8Imm8Effect 0x11aab4 4 8 0xf)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11aab4 4 8 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11aab4 0x41 0xe0 0xf (by decide) (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x11aab8 [0x44, 0x88, 0x44, 0x24, 0x06] (StorePre 0x11aab8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x11aab8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aab8 5 8 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aab8 5 8 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aab8 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x11aabd [0x40, 0xC0, 0xEF, 0x04] (fun s => s.RIP = 0x11aabd) (shrR8Effect 0x11aabd 4 7 4)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR8Effect_footprint 0x11aabd 4 7 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11aabd 0x40 0xef 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x11aac1 [0x40, 0x88, 0x7C, 0x24, 0x07] (StorePre 0x11aac1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x11aac1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aac1 5 7 (.sib 4 none 0 (.d8 0x7)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aac1 5 7 (.sib 4 none 0 (.d8 0x7))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aac1 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x7)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f35 : InstrSpec 0x11aac6 [0x89, 0xF7] (fun s => s.RIP = 0x11aac6) (movR32R32Effect 0x11aac6 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11aac6 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11aac6 0xf7 (by decide)) pre_rip
  have f36 : InstrSpec 0x11aac8 [0xC1, 0xEF, 0x18] (fun s => s.RIP = 0x11aac8) (shrR32Effect 0x11aac8 3 7 24)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x11aac8 3 7 24).toInstrSpec (shr_r32_imm8_effect_step 0x11aac8 0xef 0x18 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x11aacb [0x40, 0x80, 0xE7, 0x0F] (fun s => s.RIP = 0x11aacb) (andR8Imm8Effect 0x11aacb 4 7 0xf)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11aacb 4 7 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11aacb 0x40 0xe7 0xf (by decide) (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x11aacf [0x40, 0x88, 0x7C, 0x24, 0x08] (StorePre 0x11aacf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11aacf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aacf 5 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aacf 5 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aacf 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f39 : InstrSpec 0x11aad4 [0x89, 0xF7] (fun s => s.RIP = 0x11aad4) (movR32R32Effect 0x11aad4 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11aad4 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11aad4 0xf7 (by decide)) pre_rip
  refine Rest.ofInside (n := 89) (RestInside.exec (n := 89) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 87), (8, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa8e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f21 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 90), (8, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa91) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.out (n := 92) f22 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 93) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 92), (8, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa95) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f23 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 92), (8, 94), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa98) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f24 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 92), (8, 96), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa9c) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.exec (n := 98) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 92), (8, 96), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aaa1) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f26 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 99), (8, 96), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aaa5) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.exec (n := 101) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 99), (8, 96), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aaaa) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 102), (8, 96), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aaad) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f29 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 104), (8, 96), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aab1) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f30 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 104), (8, 106), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aab4) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f31 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 104), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aab8) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.exec (n := 110) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 104), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aabd) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f33 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 111), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aac1) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 111), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aac6) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 114) (RestInside.out (n := 114) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 115) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 114), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aac8) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 116) (RestInside.out (n := 116) f36 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 117) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 116), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aacb) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 118) (RestInside.out (n := 118) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 119) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 118), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aacf) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 120) (RestInside.exec (n := 120) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 118), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aad4) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f39 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 121), (8, 108), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aad6) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11aa40_2 code

theorem rest_l11aa40 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11aa40 bytes_l11aa40) (entryMap (live .l11aa40))
      117 0x11aa40 bytes_l11aa40 b_l11aa40 := by
  have f0 : InstrSpec 0x11aa40 [0x48, 0x83, 0xEC, 0x21] (fun s => s.RIP = 0x11aa40) (subR64Imm8Effect 0x11aa40 4 0x21)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x11aa40 4 0x21).toInstrSpec (sub_r64_imm8_effect_step 0x11aa40 0x48 0xec 0x21 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11aa44 [0x48, 0x89, 0xF8] (fun s => s.RIP = 0x11aa44) (movR64R64Effect 0x11aa44 0 7)
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x11aa44 0 7).toInstrSpec (mov_r64_r64_effect_step 0x11aa44 0x48 0xf8 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x11aa47 [0xC6, 0x44, 0x24, 0x20, 0x00] (StorePre 0x11aa47 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11aa47 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x11aa47 (.sib 4 none 0 (.d8 0x20)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM8Imm8Effect_footprint 0x11aa47 (.sib 4 none 0 (.d8 0x20)) 0x0).toInstrSpec (mov_m8_imm8_effect_step 0x11aa47 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x11aa4c [0x48, 0x8B, 0x56, 0x08] (LoadPre 0x11aa4c (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11aa4c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11aa4c 2 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11aa4c 2 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11aa4c 0x48 (by decide) 2 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x11aa50 [0x48, 0x0F, 0xCA] (fun s => s.RIP = 0x11aa50) (bswapR64Effect 0x11aa50 3 2)
      [.gpr 2] [] [.reg 2, .rip] :=
    (bswapR64Effect_footprint 0x11aa50 3 2).toInstrSpec (bswap_r64_effect_step 0x11aa50 0x48 (by decide) 0xca (by decide)) pre_rip
  have f5 : InstrSpec 0x11aa53 [0x48, 0x8B, 0x36] (LoadPre 0x11aa53 (fun s => AddrMode.addr (.base 6 .none) s (0x11aa53 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11aa53 6 (.base 6 .none))
      [.gpr 6] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x11aa53 6 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11aa53 0x48 (by decide) 6 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x11aa56 [0x48, 0x0F, 0xCE] (fun s => s.RIP = 0x11aa56) (bswapR64Effect 0x11aa56 3 6)
      [.gpr 6] [] [.reg 6, .rip] :=
    (bswapR64Effect_footprint 0x11aa56 3 6).toInstrSpec (bswap_r64_effect_step 0x11aa56 0x48 (by decide) 0xce (by decide)) pre_rip
  have f7 : InstrSpec 0x11aa59 [0x48, 0x89, 0xF1] (fun s => s.RIP = 0x11aa59) (movR64R64Effect 0x11aa59 1 6)
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64R64Effect_footprint 0x11aa59 1 6).toInstrSpec (mov_r64_r64_effect_step 0x11aa59 0x48 0xf1 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11aa5c [0x48, 0xC1, 0xE9, 0x38] (fun s => s.RIP = 0x11aa5c) (shrR64Effect 0x11aa5c 4 1 56)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR64Effect_footprint 0x11aa5c 4 1 56).toInstrSpec (shr_r64_imm8_effect_step 0x11aa5c 0x48 0xe9 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x11aa60 [0x80, 0xE1, 0x0F] (fun s => s.RIP = 0x11aa60) (andR8Imm8Effect 0x11aa60 3 1 0xf)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11aa60 3 1 0xf).toInstrSpec (and_r8_imm8_effect_step 0x11aa60 0xe1 0xf (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11aa63 [0x88, 0x0C, 0x24] (StorePre 0x11aa63 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11aa63 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11aa63 3 1 (.sib 4 none 0 .none))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aa63 3 1 (.sib 4 none 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x11aa63 1 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x11aa66 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x11aa66) (movR64R64Effect 0x11aa66 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11aa66 7 6).toInstrSpec (mov_r64_r64_effect_step 0x11aa66 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x11aa69 [0x48, 0xC1, 0xEF, 0x3C] (fun s => s.RIP = 0x11aa69) (shrR64Effect 0x11aa69 4 7 60)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x11aa69 4 7 60).toInstrSpec (shr_r64_imm8_effect_step 0x11aa69 0x48 0xef 0x3c (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11aa6d [0x40, 0x88, 0x7C, 0x24, 0x01] (StorePre 0x11aa6d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1)) s (0x11aa6d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aa6d 5 7 (.sib 4 none 0 (.d8 0x1)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aa6d 5 7 (.sib 4 none 0 (.d8 0x1))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aa6d 0x40 (by decide) 7 (.sib 4 none 0 (.d8 0x1)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x11aa72 [0x48, 0x89, 0xF7] (fun s => s.RIP = 0x11aa72) (movR64R64Effect 0x11aa72 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x11aa72 7 6).toInstrSpec (mov_r64_r64_effect_step 0x11aa72 0x48 0xf7 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x11aa75 [0x48, 0xC1, 0xEF, 0x30] (fun s => s.RIP = 0x11aa75) (shrR64Effect 0x11aa75 4 7 48)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR64Effect_footprint 0x11aa75 4 7 48).toInstrSpec (shr_r64_imm8_effect_step 0x11aa75 0x48 0xef 0x30 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11aa79 [0x41, 0x89, 0xF8] (fun s => s.RIP = 0x11aa79) (movR32R32Effect 0x11aa79 3 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x11aa79 3 8 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x11aa79 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x11aa7c [0x41, 0x80, 0xE0, 0x0F] (fun s => s.RIP = 0x11aa7c) (andR8Imm8Effect 0x11aa7c 4 8 0xf)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11aa7c 4 8 0xf).toInstrSpec (and_r8_imm8_rex_effect_step 0x11aa7c 0x41 0xe0 0xf (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x11aa80 [0x44, 0x88, 0x44, 0x24, 0x02] (StorePre 0x11aa80 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x11aa80 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aa80 5 8 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x11aa80 5 8 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11aa80 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x11aa85 [0x40, 0xC0, 0xEF, 0x04] (fun s => s.RIP = 0x11aa85) (shrR8Effect 0x11aa85 4 7 4)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR8Effect_footprint 0x11aa85 4 7 4).toInstrSpec (shr_r8_imm8_rex_effect_step 0x11aa85 0x40 0xef 0x4 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa44) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa47) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa4c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (2, 58), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa50) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (2, 60), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa53) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (2, 60), (3, 3), (4, 53), (5, 5), (6, 62), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa56) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa59) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 55), (1, 66), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa5c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 55), (1, 68), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa60) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa63) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa66) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa69) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa6d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 75), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa72) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa75) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 80), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa79) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa7c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 80), (8, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa80) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.exec (n := 86) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 80), (8, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa85) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 55), (1, 70), (2, 60), (3, 3), (4, 53), (5, 5), (6, 64), (7, 87), (8, 84), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11aa89) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l11aa40_1 code

theorem block_l11aa40 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11aa40 :=
  Rest.liftedBlock (rest_l11aa40 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11aa40 x hx)

theorem rest_l11ac00 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11ac00 bytes_l11ac00) (entryMap (live .l11ac00))
      18 0x11ac00 bytes_l11ac00 b_l11ac00 := by
  have f0 : InstrSpec 0x11ac00 [0x8D, 0x71, 0x08] (fun s => s.RIP = 0x11ac00) (leaR32Effect 0x11ac00 3 6 (.base 1 (.d8 0x8)))
      [.gpr 1] [] [.reg 6, .rip] :=
    (leaR32Effect_footprint 0x11ac00 3 6 (.base 1 (.d8 0x8))).toInstrSpec (lea_r32_effect_step 0x11ac00 6 (.base 1 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x11ac03 [0x89, 0xF7] (fun s => s.RIP = 0x11ac03) (movR32R32Effect 0x11ac03 2 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11ac03 2 7 6).toInstrSpec (mov_r32_r32_effect_step 0x11ac03 0xf7 (by decide)) pre_rip
  have f2 : InstrSpec 0x11ac05 [0x40, 0x80, 0xE7, 0xF0] (fun s => s.RIP = 0x11ac05) (andR8Imm8Effect 0x11ac05 4 7 0xf0)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11ac05 4 7 0xf0).toInstrSpec (and_r8_imm8_rex_effect_step 0x11ac05 0x40 0xe7 0xf0 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x11ac09 [0x40, 0x28, 0xF9] (fun s => s.RIP = 0x11ac09) (subR8R8Effect 0x11ac09 3 1 7)
      [.gpr 1, .gpr 7] [] [.reg 1, .flags, .rip] :=
    (subR8R8Effect_footprint 0x11ac09 3 1 7).toInstrSpec (sub_r8_r8_rex_effect_step 0x11ac09 0x40 0xf9 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x11ac0c [0x88, 0x4C, 0x14, 0xFE] (StorePre 0x11ac0c 4 (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d8 0xfe)) s (0x11ac0c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11ac0c 4 1 (.sib 4 (some 2) 0 (.d8 0xfe)))
      [.gpr 1, .gpr 4, .gpr 2] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ac0c 4 1 (.sib 4 (some 2) 0 (.d8 0xfe))).toInstrSpec (mov_m8_r8_effect_step 0x11ac0c 1 (by decide) (.sib 4 (some 2) 0 (.d8 0xfe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x11ac10 [0x40, 0xC0, 0xFE, 0x04] (fun s => s.RIP = 0x11ac10) (sarR8Effect 0x11ac10 4 6 4)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (sarR8Effect_footprint 0x11ac10 4 6 4).toInstrSpec (sar_r8_imm8_rex_effect_step 0x11ac10 0x40 0xfe 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x11ac14 [0x40, 0x02, 0x74, 0x14, 0xFF] (LoadPre 0x11ac14 (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d8 0xff)) s (0x11ac14 + BitVec.ofNat 64 5)) 1) (addR8M8Effect 0x11ac14 5 6 (.sib 4 (some 2) 0 (.d8 0xff)))
      [.gpr 6, .gpr 4, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (addR8M8Effect_footprint 0x11ac14 5 6 (.sib 4 (some 2) 0 (.d8 0xff))).toInstrSpec (add_r8_m8_rex_effect_step 0x11ac14 0x40 (by decide) 6 (.sib 4 (some 2) 0 (.d8 0xff)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x11ac19 [0x8D, 0x4E, 0x08] (fun s => s.RIP = 0x11ac19) (leaR32Effect 0x11ac19 3 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (leaR32Effect_footprint 0x11ac19 3 1 (.base 6 (.d8 0x8))).toInstrSpec (lea_r32_effect_step 0x11ac19 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x11ac1c [0x89, 0xCF] (fun s => s.RIP = 0x11ac1c) (movR32R32Effect 0x11ac1c 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x11ac1c 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x11ac1c 0xcf (by decide)) pre_rip
  have f9 : InstrSpec 0x11ac1e [0x40, 0x80, 0xE7, 0xF0] (fun s => s.RIP = 0x11ac1e) (andR8Imm8Effect 0x11ac1e 4 7 0xf0)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR8Imm8Effect_footprint 0x11ac1e 4 7 0xf0).toInstrSpec (and_r8_imm8_rex_effect_step 0x11ac1e 0x40 0xe7 0xf0 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x11ac22 [0x40, 0x28, 0xFE] (fun s => s.RIP = 0x11ac22) (subR8R8Effect 0x11ac22 3 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (subR8R8Effect_footprint 0x11ac22 3 6 7).toInstrSpec (sub_r8_r8_rex_effect_step 0x11ac22 0x40 0xfe (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11ac25 [0x40, 0x88, 0x74, 0x14, 0xFF] (StorePre 0x11ac25 5 (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d8 0xff)) s (0x11ac25 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ac25 5 6 (.sib 4 (some 2) 0 (.d8 0xff)))
      [.gpr 6, .gpr 4, .gpr 2] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ac25 5 6 (.sib 4 (some 2) 0 (.d8 0xff))).toInstrSpec (mov_m8_r8_rex_effect_step 0x11ac25 0x40 (by decide) 6 (.sib 4 (some 2) 0 (.d8 0xff)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x11ac2a [0xC0, 0xF9, 0x04] (fun s => s.RIP = 0x11ac2a) (sarR8Effect 0x11ac2a 3 1 4)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (sarR8Effect_footprint 0x11ac2a 3 1 4).toInstrSpec (sar_r8_imm8_effect_step 0x11ac2a 0xf9 0x4 (by decide) (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x11ac2d [0x02, 0x0C, 0x14] (LoadPre 0x11ac2d (fun s => AddrMode.addr (.sib 4 (some 2) 0 .none) s (0x11ac2d + BitVec.ofNat 64 3)) 1) (addR8M8Effect 0x11ac2d 3 1 (.sib 4 (some 2) 0 .none))
      [.gpr 1, .gpr 4, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (addR8M8Effect_footprint 0x11ac2d 3 1 (.sib 4 (some 2) 0 .none)).toInstrSpec (add_r8_m8_effect_step 0x11ac2d 1 (by decide) (.sib 4 (some 2) 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x11ac30 [0x88, 0x0C, 0x14] (StorePre 0x11ac30 3 (fun s => AddrMode.addr (.sib 4 (some 2) 0 .none) s (0x11ac30 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11ac30 3 1 (.sib 4 (some 2) 0 .none))
      [.gpr 1, .gpr 4, .gpr 2] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ac30 3 1 (.sib 4 (some 2) 0 .none)).toInstrSpec (mov_m8_r8_effect_step 0x11ac30 1 (by decide) (.sib 4 (some 2) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x11ac33 [0x48, 0x83, 0xC2, 0x02] (fun s => s.RIP = 0x11ac33) (addR64Imm8Effect 0x11ac33 2 0x2)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11ac33 2 0x2).toInstrSpec (add_r64_imm8_effect_step 0x11ac33 0x48 0xc2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x11ac37 [0x48, 0x83, 0xFA, 0x22] (fun s => s.RIP = 0x11ac37) (cmpR64Imm8Effect 0x11ac37 2 0x22)
      [.gpr 2] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x11ac37 2 0x22).toInstrSpec (cmp_r64_imm8_effect_step 0x11ac37 0x48 0xfa 0x22 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac03) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac05) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac09) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac0c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 53), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac10) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 62), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac14) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 64), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac19) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 66), (2, 2), (3, 3), (4, 4), (5, 5), (6, 64), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac1c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 66), (2, 2), (3, 3), (4, 4), (5, 5), (6, 64), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac1e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 66), (2, 2), (3, 3), (4, 4), (5, 5), (6, 64), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac22) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 66), (2, 2), (3, 3), (4, 4), (5, 5), (6, 72), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac25) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 66), (2, 2), (3, 3), (4, 4), (5, 5), (6, 72), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac2a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f12 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 75), (2, 2), (3, 3), (4, 4), (5, 5), (6, 72), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac2d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 72), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac30) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 77), (2, 2), (3, 3), (4, 4), (5, 5), (6, 72), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac33) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 77), (2, 80), (3, 3), (4, 4), (5, 5), (6, 72), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac37) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 0), (1, 77), (2, 80), (3, 3), (4, 4), (5, 5), (6, 72), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac3b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 84) (jcc_rel8_effect_step 0x11ac3b 5 0xc3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l11ac00 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11ac00 :=
  Rest.liftedBlock (rest_l11ac00 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11ac00 x hx)

theorem rest_l11ac3d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x11ac3d bytes_l11ac3d) (entryMap (live .l11ac3d))
      12 0x11ac3d bytes_l11ac3d b_l11ac3d := by
  have f0 : InstrSpec 0x11ac3d [0x0F, 0xB6, 0x4C, 0x24, 0x20] (LoadPre 0x11ac3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11ac3d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11ac3d 5 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x11ac3d 5 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (movzx_r32_m8_effect_step 0x11ac3d 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x11ac42 [0x88, 0x48, 0x20] (StorePre 0x11ac42 3 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x11ac42 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11ac42 3 1 (.base 0 (.d8 0x20)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM8R8Effect_footprint 0x11ac42 3 1 (.base 0 (.d8 0x20))).toInstrSpec (mov_m8_r8_effect_step 0x11ac42 1 (by decide) (.base 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x11ac45 [0x48, 0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x11ac45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ac45 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ac45 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11ac45 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x11ac45 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x11ac4a [0x48, 0x89, 0x48, 0x18] (StorePre 0x11ac4a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x11ac4a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ac4a 1 (.base 0 (.d8 0x18)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ac4a 1 (.base 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x11ac4a 0x48 (by decide) 1 (.base 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x11ac4e [0x48, 0x8B, 0x4C, 0x24, 0x10] (LoadPre 0x11ac4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ac4e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ac4e 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11ac4e 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x11ac4e 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x11ac53 [0x48, 0x89, 0x48, 0x10] (StorePre 0x11ac53 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x11ac53 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ac53 1 (.base 0 (.d8 0x10)))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ac53 1 (.base 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x11ac53 0x48 (by decide) 1 (.base 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x11ac57 [0x48, 0x8B, 0x0C, 0x24] (LoadPre 0x11ac57 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11ac57 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11ac57 1 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x11ac57 1 (.sib 4 none 0 .none)).toInstrSpec (mov_r64_m64_effect_step 0x11ac57 0x48 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x11ac5b [0x48, 0x8B, 0x54, 0x24, 0x08] (LoadPre 0x11ac5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ac5b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ac5b 2 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x11ac5b 2 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x11ac5b 0x48 (by decide) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x11ac60 [0x48, 0x89, 0x50, 0x08] (StorePre 0x11ac60 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x11ac60 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ac60 2 (.base 0 (.d8 0x8)))
      [.gpr 2, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ac60 2 (.base 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x11ac60 0x48 (by decide) 2 (.base 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x11ac64 [0x48, 0x89, 0x08] (StorePre 0x11ac64 3 (fun s => AddrMode.addr (.base 0 .none) s (0x11ac64 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11ac64 1 (.base 0 .none))
      [.gpr 1, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x11ac64 1 (.base 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x11ac64 0x48 (by decide) 1 (.base 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x11ac67 [0x48, 0x83, 0xC4, 0x21] (fun s => s.RIP = 0x11ac67) (addR64Imm8Effect 0x11ac67 4 0x21)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x11ac67 4 0x21).toInstrSpec (add_r64_imm8_effect_step 0x11ac67 0x48 0xc4 0x21 (by decide) (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x11ac6b [0xC3] (RetPre 0x11ac6b) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x11ac6b).toInstrSpec (ret_effect_step 0x11ac6b) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac42) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac45) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac4a) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 56), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac4e) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac53) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac57) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac5b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac60) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac64) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac67) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 68), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x11ac6b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 71) f11 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 72) (ρ' := [(0, 0), (1, 62), (2, 64), (3, 3), (4, 71), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f11 (by decide) rfl rfl rfl (by decide)

theorem block_l11ac3d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l11ac3d :=
  Rest.liftedBlock (rest_l11ac3d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l11ac3d x hx)

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

theorem_by block_l11aa40_eval :
    program.runBlock (dialect code) ⟨.l11aa40, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11ac00_eval :
    program.runBlock (dialect code) ⟨.l11ac00, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l11ac3d_eval :
    program.runBlock (dialect code) ⟨.l11ac3d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end K256.Proofs.Ecdh.LIR
