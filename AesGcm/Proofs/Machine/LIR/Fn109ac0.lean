import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l109ac0_7 [Bindings] (code : CodeMap) :
    Rest (n := 262) code lifted (codeRange 0x109ac0 bytes_l109ac0) [(0, 256), (1, 258), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      12 0x109d4a bytes_l109ac0_7 b_l109ac0_7 := by
  have f140 : InstrSpec 0x109d4a [0x0F, 0xB6, 0x44, 0x24, 0x3D] (LoadPre 0x109d4a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3d)) s (0x109d4a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d4a 5 0 (.sib 4 none 0 (.d8 0x3d)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109d4a 5 0 (.sib 4 none 0 (.d8 0x3d))).toInstrSpec (movzx_r32_m8_effect_step 0x109d4a 0 (.sib 4 none 0 (.d8 0x3d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f141 : InstrSpec 0x109d4f [0x0F, 0xB6, 0x4C, 0x24, 0x42] (LoadPre 0x109d4f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x109d4f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d4f 5 1 (.sib 4 none 0 (.d8 0x42)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109d4f 5 1 (.sib 4 none 0 (.d8 0x42))).toInstrSpec (movzx_r32_m8_effect_step 0x109d4f 1 (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f142 : InstrSpec 0x109d54 [0x88, 0x4C, 0x24, 0x3D] (StorePre 0x109d54 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3d)) s (0x109d54 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d54 4 1 (.sib 4 none 0 (.d8 0x3d)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d54 4 1 (.sib 4 none 0 (.d8 0x3d))).toInstrSpec (mov_m8_r8_effect_step 0x109d54 1 (by decide) (.sib 4 none 0 (.d8 0x3d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f143 : InstrSpec 0x109d58 [0x88, 0x44, 0x24, 0x42] (StorePre 0x109d58 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x109d58 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d58 4 0 (.sib 4 none 0 (.d8 0x42)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d58 4 0 (.sib 4 none 0 (.d8 0x42))).toInstrSpec (mov_m8_r8_effect_step 0x109d58 0 (by decide) (.sib 4 none 0 (.d8 0x42)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f144 : InstrSpec 0x109d5c [0x0F, 0xB6, 0x44, 0x24, 0x3E] (LoadPre 0x109d5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x109d5c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d5c 5 0 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109d5c 5 0 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (movzx_r32_m8_effect_step 0x109d5c 0 (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f145 : InstrSpec 0x109d61 [0x0F, 0xB6, 0x4C, 0x24, 0x41] (LoadPre 0x109d61 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x109d61 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d61 5 1 (.sib 4 none 0 (.d8 0x41)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109d61 5 1 (.sib 4 none 0 (.d8 0x41))).toInstrSpec (movzx_r32_m8_effect_step 0x109d61 1 (.sib 4 none 0 (.d8 0x41)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f146 : InstrSpec 0x109d66 [0x88, 0x4C, 0x24, 0x3E] (StorePre 0x109d66 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x109d66 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d66 4 1 (.sib 4 none 0 (.d8 0x3e)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d66 4 1 (.sib 4 none 0 (.d8 0x3e))).toInstrSpec (mov_m8_r8_effect_step 0x109d66 1 (by decide) (.sib 4 none 0 (.d8 0x3e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f147 : InstrSpec 0x109d6a [0x88, 0x44, 0x24, 0x41] (StorePre 0x109d6a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x109d6a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d6a 4 0 (.sib 4 none 0 (.d8 0x41)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d6a 4 0 (.sib 4 none 0 (.d8 0x41))).toInstrSpec (mov_m8_r8_effect_step 0x109d6a 0 (by decide) (.sib 4 none 0 (.d8 0x41)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f148 : InstrSpec 0x109d6e [0x66, 0xC1, 0x44, 0x24, 0x3F, 0x08] (StorePre 0x109d6e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x109d6e + BitVec.ofNat 64 6)) 2) (rolMEffect 0x109d6e 6 16 (.sib 4 none 0 (.d8 0x3f)) 8)
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (rolMEffect16_footprint 0x109d6e 6 (.sib 4 none 0 (.d8 0x3f)) 8).toInstrSpec (rol_m16_imm8_effect_step 0x109d6e (.sib 4 none 0 (.d8 0x3f)) (by decide) (by decide) (by decide) 0x8) (StorePre.of_addr rfl)
  have f149 : InstrSpec 0x109d74 [0x48, 0x8B, 0x3F] (LoadPre 0x109d74 (fun s => AddrMode.addr (.base 7 .none) s (0x109d74 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109d74 7 (.base 7 .none))
      [.gpr 7] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x109d74 7 (.base 7 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109d74 0x48 (by decide) 7 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f150 : InstrSpec 0x109d77 [0x48, 0x8D, 0x74, 0x24, 0x08] (fun s => s.RIP = 0x109d77) (leaR64Effect 0x109d77 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (leaR64Effect_footprint 0x109d77 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (lea_r64_effect_step 0x109d77 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) pre_rip
  have f151 : InstrSpec 0x109d7c [0xE8, 0x4F, 0x97, 0xFF, 0xFF] (PushPre 0x109d7c 5) (callEffect (fun _ => 0x1034d0) 0x109d81)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x109d7c 0x1034d0 0x109d81).toInstrSpec (call_rel32_effect_step 0x109d7c 0xffff974f (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 262) (RestInside.out (n := 262) f140 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 263) (ρ' := [(0, 262), (1, 258), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d4f) f140 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 264) (RestInside.out (n := 264) f141 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 265) (ρ' := [(0, 262), (1, 264), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d54) f141 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 266) (RestInside.exec (n := 266) (ρ' := [(0, 262), (1, 264), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d58) f142 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 267) (RestInside.exec (n := 267) (ρ' := [(0, 262), (1, 264), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d5c) f143 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f144 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 268), (1, 264), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d61) f144 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f145 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 268), (1, 270), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d66) f145 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.exec (n := 272) (ρ' := [(0, 268), (1, 270), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d6a) f146 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 273) (RestInside.exec (n := 273) (ρ' := [(0, 268), (1, 270), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d6e) f147 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 274) (RestInside.exec (n := 274) (ρ' := [(0, 268), (1, 270), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d74) f148 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 275) (RestInside.out (n := 275) f149 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 276) (ρ' := [(0, 268), (1, 270), (3, 3), (4, 53), (5, 5), (6, 6), (7, 275), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d77) f149 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 277) (RestInside.out (n := 277) f150 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 278) (ρ' := [(0, 268), (1, 270), (3, 3), (4, 53), (5, 5), (6, 277), (7, 275), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d7c) f150 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 279) (RestInside.out (n := 279) f151 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 280) (ρ' := [(0, 268), (1, 270), (3, 3), (4, 279), (5, 5), (6, 277), (7, 275), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1034d0) f151 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 281) (by decide) (by decide) rfl rfl

theorem rest_l109ac0_6 [Bindings] (code : CodeMap) :
    Rest (n := 232) code lifted (codeRange 0x109ac0 bytes_l109ac0) [(0, 225), (1, 227), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      32 0x109cf0 bytes_l109ac0_6 b_l109ac0_6 := by
  have f120 : InstrSpec 0x109cf0 [0x0F, 0xB6, 0x44, 0x24, 0x38] (LoadPre 0x109cf0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109cf0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cf0 5 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109cf0 5 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (movzx_r32_m8_effect_step 0x109cf0 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f121 : InstrSpec 0x109cf5 [0x0F, 0xB6, 0x4C, 0x24, 0x47] (LoadPre 0x109cf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x109cf5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cf5 5 1 (.sib 4 none 0 (.d8 0x47)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109cf5 5 1 (.sib 4 none 0 (.d8 0x47))).toInstrSpec (movzx_r32_m8_effect_step 0x109cf5 1 (.sib 4 none 0 (.d8 0x47)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f122 : InstrSpec 0x109cfa [0x88, 0x4C, 0x24, 0x38] (StorePre 0x109cfa 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109cfa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cfa 4 1 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109cfa 4 1 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m8_r8_effect_step 0x109cfa 1 (by decide) (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f123 : InstrSpec 0x109cfe [0x88, 0x44, 0x24, 0x47] (StorePre 0x109cfe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x109cfe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cfe 4 0 (.sib 4 none 0 (.d8 0x47)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109cfe 4 0 (.sib 4 none 0 (.d8 0x47))).toInstrSpec (mov_m8_r8_effect_step 0x109cfe 0 (by decide) (.sib 4 none 0 (.d8 0x47)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f124 : InstrSpec 0x109d02 [0x0F, 0xB6, 0x44, 0x24, 0x39] (LoadPre 0x109d02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x109d02 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d02 5 0 (.sib 4 none 0 (.d8 0x39)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109d02 5 0 (.sib 4 none 0 (.d8 0x39))).toInstrSpec (movzx_r32_m8_effect_step 0x109d02 0 (.sib 4 none 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f125 : InstrSpec 0x109d07 [0x0F, 0xB6, 0x4C, 0x24, 0x46] (LoadPre 0x109d07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x109d07 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d07 5 1 (.sib 4 none 0 (.d8 0x46)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109d07 5 1 (.sib 4 none 0 (.d8 0x46))).toInstrSpec (movzx_r32_m8_effect_step 0x109d07 1 (.sib 4 none 0 (.d8 0x46)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f126 : InstrSpec 0x109d0c [0x88, 0x4C, 0x24, 0x39] (StorePre 0x109d0c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x109d0c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d0c 4 1 (.sib 4 none 0 (.d8 0x39)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d0c 4 1 (.sib 4 none 0 (.d8 0x39))).toInstrSpec (mov_m8_r8_effect_step 0x109d0c 1 (by decide) (.sib 4 none 0 (.d8 0x39)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f127 : InstrSpec 0x109d10 [0x88, 0x44, 0x24, 0x46] (StorePre 0x109d10 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x109d10 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d10 4 0 (.sib 4 none 0 (.d8 0x46)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d10 4 0 (.sib 4 none 0 (.d8 0x46))).toInstrSpec (mov_m8_r8_effect_step 0x109d10 0 (by decide) (.sib 4 none 0 (.d8 0x46)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f128 : InstrSpec 0x109d14 [0x0F, 0xB6, 0x44, 0x24, 0x3A] (LoadPre 0x109d14 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x109d14 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d14 5 0 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109d14 5 0 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (movzx_r32_m8_effect_step 0x109d14 0 (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f129 : InstrSpec 0x109d19 [0x0F, 0xB6, 0x4C, 0x24, 0x45] (LoadPre 0x109d19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x109d19 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d19 5 1 (.sib 4 none 0 (.d8 0x45)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109d19 5 1 (.sib 4 none 0 (.d8 0x45))).toInstrSpec (movzx_r32_m8_effect_step 0x109d19 1 (.sib 4 none 0 (.d8 0x45)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f130 : InstrSpec 0x109d1e [0x88, 0x4C, 0x24, 0x3A] (StorePre 0x109d1e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x109d1e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d1e 4 1 (.sib 4 none 0 (.d8 0x3a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d1e 4 1 (.sib 4 none 0 (.d8 0x3a))).toInstrSpec (mov_m8_r8_effect_step 0x109d1e 1 (by decide) (.sib 4 none 0 (.d8 0x3a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f131 : InstrSpec 0x109d22 [0x88, 0x44, 0x24, 0x45] (StorePre 0x109d22 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x109d22 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d22 4 0 (.sib 4 none 0 (.d8 0x45)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d22 4 0 (.sib 4 none 0 (.d8 0x45))).toInstrSpec (mov_m8_r8_effect_step 0x109d22 0 (by decide) (.sib 4 none 0 (.d8 0x45)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f132 : InstrSpec 0x109d26 [0x0F, 0xB6, 0x44, 0x24, 0x3B] (LoadPre 0x109d26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3b)) s (0x109d26 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d26 5 0 (.sib 4 none 0 (.d8 0x3b)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109d26 5 0 (.sib 4 none 0 (.d8 0x3b))).toInstrSpec (movzx_r32_m8_effect_step 0x109d26 0 (.sib 4 none 0 (.d8 0x3b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f133 : InstrSpec 0x109d2b [0x0F, 0xB6, 0x4C, 0x24, 0x44] (LoadPre 0x109d2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x109d2b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d2b 5 1 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109d2b 5 1 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (movzx_r32_m8_effect_step 0x109d2b 1 (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f134 : InstrSpec 0x109d30 [0x88, 0x4C, 0x24, 0x3B] (StorePre 0x109d30 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3b)) s (0x109d30 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d30 4 1 (.sib 4 none 0 (.d8 0x3b)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d30 4 1 (.sib 4 none 0 (.d8 0x3b))).toInstrSpec (mov_m8_r8_effect_step 0x109d30 1 (by decide) (.sib 4 none 0 (.d8 0x3b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f135 : InstrSpec 0x109d34 [0x88, 0x44, 0x24, 0x44] (StorePre 0x109d34 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x109d34 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d34 4 0 (.sib 4 none 0 (.d8 0x44)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d34 4 0 (.sib 4 none 0 (.d8 0x44))).toInstrSpec (mov_m8_r8_effect_step 0x109d34 0 (by decide) (.sib 4 none 0 (.d8 0x44)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f136 : InstrSpec 0x109d38 [0x0F, 0xB6, 0x44, 0x24, 0x3C] (LoadPre 0x109d38 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x109d38 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d38 5 0 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109d38 5 0 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (movzx_r32_m8_effect_step 0x109d38 0 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f137 : InstrSpec 0x109d3d [0x0F, 0xB6, 0x4C, 0x24, 0x43] (LoadPre 0x109d3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x109d3d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d3d 5 1 (.sib 4 none 0 (.d8 0x43)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109d3d 5 1 (.sib 4 none 0 (.d8 0x43))).toInstrSpec (movzx_r32_m8_effect_step 0x109d3d 1 (.sib 4 none 0 (.d8 0x43)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f138 : InstrSpec 0x109d42 [0x88, 0x4C, 0x24, 0x3C] (StorePre 0x109d42 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x109d42 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d42 4 1 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d42 4 1 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m8_r8_effect_step 0x109d42 1 (by decide) (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f139 : InstrSpec 0x109d46 [0x88, 0x44, 0x24, 0x43] (StorePre 0x109d46 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x109d46 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d46 4 0 (.sib 4 none 0 (.d8 0x43)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109d46 4 0 (.sib 4 none 0 (.d8 0x43))).toInstrSpec (mov_m8_r8_effect_step 0x109d46 0 (by decide) (.sib 4 none 0 (.d8 0x43)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f120 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 232), (1, 227), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cf5) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f121 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 232), (1, 234), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cfa) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.exec (n := 236) (ρ' := [(0, 232), (1, 234), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cfe) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 237) (RestInside.exec (n := 237) (ρ' := [(0, 232), (1, 234), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d02) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f124 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 238), (1, 234), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d07) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f125 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 238), (1, 240), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d0c) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.exec (n := 242) (ρ' := [(0, 238), (1, 240), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d10) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 243) (RestInside.exec (n := 243) (ρ' := [(0, 238), (1, 240), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d14) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f128 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 244), (1, 240), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d19) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 246) (RestInside.out (n := 246) f129 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 247) (ρ' := [(0, 244), (1, 246), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d1e) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 248) (RestInside.exec (n := 248) (ρ' := [(0, 244), (1, 246), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d22) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 249) (RestInside.exec (n := 249) (ρ' := [(0, 244), (1, 246), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d26) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 250) (RestInside.out (n := 250) f132 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 251) (ρ' := [(0, 250), (1, 246), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d2b) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 252) (RestInside.out (n := 252) f133 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 253) (ρ' := [(0, 250), (1, 252), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d30) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 254) (RestInside.exec (n := 254) (ρ' := [(0, 250), (1, 252), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d34) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 255) (RestInside.exec (n := 255) (ρ' := [(0, 250), (1, 252), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d38) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 256) (RestInside.out (n := 256) f136 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 257) (ρ' := [(0, 256), (1, 252), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d3d) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 258) (RestInside.out (n := 258) f137 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 259) (ρ' := [(0, 256), (1, 258), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d42) f137 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 260) (RestInside.exec (n := 260) (ρ' := [(0, 256), (1, 258), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d46) f138 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 261) (RestInside.exec (n := 261) (ρ' := [(0, 256), (1, 258), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d4a) f139 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109ac0_7 code

theorem rest_l109ac0_5 [Bindings] (code : CodeMap) :
    Rest (n := 203) code lifted (codeRange 0x109ac0 bytes_l109ac0) [(0, 201), (1, 197), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      52 0x109c95 bytes_l109ac0_5 b_l109ac0_5 := by
  have f100 : InstrSpec 0x109c95 [0x0F, 0xB6, 0x4C, 0x24, 0x35] (LoadPre 0x109c95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x109c95 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c95 5 1 (.sib 4 none 0 (.d8 0x35)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109c95 5 1 (.sib 4 none 0 (.d8 0x35))).toInstrSpec (movzx_r32_m8_effect_step 0x109c95 1 (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f101 : InstrSpec 0x109c9a [0x88, 0x4C, 0x24, 0x2A] (StorePre 0x109c9a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x109c9a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c9a 4 1 (.sib 4 none 0 (.d8 0x2a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c9a 4 1 (.sib 4 none 0 (.d8 0x2a))).toInstrSpec (mov_m8_r8_effect_step 0x109c9a 1 (by decide) (.sib 4 none 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f102 : InstrSpec 0x109c9e [0x88, 0x44, 0x24, 0x35] (StorePre 0x109c9e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x35)) s (0x109c9e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c9e 4 0 (.sib 4 none 0 (.d8 0x35)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c9e 4 0 (.sib 4 none 0 (.d8 0x35))).toInstrSpec (mov_m8_r8_effect_step 0x109c9e 0 (by decide) (.sib 4 none 0 (.d8 0x35)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f103 : InstrSpec 0x109ca2 [0x0F, 0xB6, 0x44, 0x24, 0x2B] (LoadPre 0x109ca2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2b)) s (0x109ca2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109ca2 5 0 (.sib 4 none 0 (.d8 0x2b)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109ca2 5 0 (.sib 4 none 0 (.d8 0x2b))).toInstrSpec (movzx_r32_m8_effect_step 0x109ca2 0 (.sib 4 none 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f104 : InstrSpec 0x109ca7 [0x0F, 0xB6, 0x4C, 0x24, 0x34] (LoadPre 0x109ca7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x109ca7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109ca7 5 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109ca7 5 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (movzx_r32_m8_effect_step 0x109ca7 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f105 : InstrSpec 0x109cac [0x88, 0x4C, 0x24, 0x2B] (StorePre 0x109cac 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2b)) s (0x109cac + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cac 4 1 (.sib 4 none 0 (.d8 0x2b)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109cac 4 1 (.sib 4 none 0 (.d8 0x2b))).toInstrSpec (mov_m8_r8_effect_step 0x109cac 1 (by decide) (.sib 4 none 0 (.d8 0x2b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f106 : InstrSpec 0x109cb0 [0x88, 0x44, 0x24, 0x34] (StorePre 0x109cb0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x109cb0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cb0 4 0 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109cb0 4 0 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_m8_r8_effect_step 0x109cb0 0 (by decide) (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f107 : InstrSpec 0x109cb4 [0x0F, 0xB6, 0x44, 0x24, 0x2C] (LoadPre 0x109cb4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x109cb4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cb4 5 0 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109cb4 5 0 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (movzx_r32_m8_effect_step 0x109cb4 0 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f108 : InstrSpec 0x109cb9 [0x0F, 0xB6, 0x4C, 0x24, 0x33] (LoadPre 0x109cb9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x109cb9 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cb9 5 1 (.sib 4 none 0 (.d8 0x33)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109cb9 5 1 (.sib 4 none 0 (.d8 0x33))).toInstrSpec (movzx_r32_m8_effect_step 0x109cb9 1 (.sib 4 none 0 (.d8 0x33)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f109 : InstrSpec 0x109cbe [0x88, 0x4C, 0x24, 0x2C] (StorePre 0x109cbe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x109cbe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cbe 4 1 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109cbe 4 1 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_m8_r8_effect_step 0x109cbe 1 (by decide) (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f110 : InstrSpec 0x109cc2 [0x88, 0x44, 0x24, 0x33] (StorePre 0x109cc2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x33)) s (0x109cc2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cc2 4 0 (.sib 4 none 0 (.d8 0x33)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109cc2 4 0 (.sib 4 none 0 (.d8 0x33))).toInstrSpec (mov_m8_r8_effect_step 0x109cc2 0 (by decide) (.sib 4 none 0 (.d8 0x33)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f111 : InstrSpec 0x109cc6 [0x0F, 0xB6, 0x44, 0x24, 0x2D] (LoadPre 0x109cc6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x109cc6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cc6 5 0 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109cc6 5 0 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (movzx_r32_m8_effect_step 0x109cc6 0 (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f112 : InstrSpec 0x109ccb [0x0F, 0xB6, 0x4C, 0x24, 0x32] (LoadPre 0x109ccb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x109ccb + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109ccb 5 1 (.sib 4 none 0 (.d8 0x32)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109ccb 5 1 (.sib 4 none 0 (.d8 0x32))).toInstrSpec (movzx_r32_m8_effect_step 0x109ccb 1 (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f113 : InstrSpec 0x109cd0 [0x88, 0x4C, 0x24, 0x2D] (StorePre 0x109cd0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2d)) s (0x109cd0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cd0 4 1 (.sib 4 none 0 (.d8 0x2d)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109cd0 4 1 (.sib 4 none 0 (.d8 0x2d))).toInstrSpec (mov_m8_r8_effect_step 0x109cd0 1 (by decide) (.sib 4 none 0 (.d8 0x2d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f114 : InstrSpec 0x109cd4 [0x88, 0x44, 0x24, 0x32] (StorePre 0x109cd4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x109cd4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cd4 4 0 (.sib 4 none 0 (.d8 0x32)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109cd4 4 0 (.sib 4 none 0 (.d8 0x32))).toInstrSpec (mov_m8_r8_effect_step 0x109cd4 0 (by decide) (.sib 4 none 0 (.d8 0x32)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f115 : InstrSpec 0x109cd8 [0x0F, 0xB6, 0x44, 0x24, 0x2E] (LoadPre 0x109cd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x109cd8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cd8 5 0 (.sib 4 none 0 (.d8 0x2e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109cd8 5 0 (.sib 4 none 0 (.d8 0x2e))).toInstrSpec (movzx_r32_m8_effect_step 0x109cd8 0 (.sib 4 none 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f116 : InstrSpec 0x109cdd [0x0F, 0xB6, 0x4C, 0x24, 0x31] (LoadPre 0x109cdd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x109cdd + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109cdd 5 1 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109cdd 5 1 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (movzx_r32_m8_effect_step 0x109cdd 1 (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f117 : InstrSpec 0x109ce2 [0x88, 0x4C, 0x24, 0x2E] (StorePre 0x109ce2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x109ce2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109ce2 4 1 (.sib 4 none 0 (.d8 0x2e)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109ce2 4 1 (.sib 4 none 0 (.d8 0x2e))).toInstrSpec (mov_m8_r8_effect_step 0x109ce2 1 (by decide) (.sib 4 none 0 (.d8 0x2e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f118 : InstrSpec 0x109ce6 [0x88, 0x44, 0x24, 0x31] (StorePre 0x109ce6 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x109ce6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109ce6 4 0 (.sib 4 none 0 (.d8 0x31)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109ce6 4 0 (.sib 4 none 0 (.d8 0x31))).toInstrSpec (mov_m8_r8_effect_step 0x109ce6 0 (by decide) (.sib 4 none 0 (.d8 0x31)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f119 : InstrSpec 0x109cea [0x66, 0xC1, 0x44, 0x24, 0x2F, 0x08] (StorePre 0x109cea 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x109cea + BitVec.ofNat 64 6)) 2) (rolMEffect 0x109cea 6 16 (.sib 4 none 0 (.d8 0x2f)) 8)
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (rolMEffect16_footprint 0x109cea 6 (.sib 4 none 0 (.d8 0x2f)) 8).toInstrSpec (rol_m16_imm8_effect_step 0x109cea (.sib 4 none 0 (.d8 0x2f)) (by decide) (by decide) (by decide) 0x8) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f100 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 201), (1, 203), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c9a) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.exec (n := 205) (ρ' := [(0, 201), (1, 203), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c9e) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 206) (RestInside.exec (n := 206) (ρ' := [(0, 201), (1, 203), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ca2) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f103 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 207), (1, 203), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ca7) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f104 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 207), (1, 209), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cac) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.exec (n := 211) (ρ' := [(0, 207), (1, 209), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cb0) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 212) (RestInside.exec (n := 212) (ρ' := [(0, 207), (1, 209), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cb4) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 213) (RestInside.out (n := 213) f107 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 214) (ρ' := [(0, 213), (1, 209), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cb9) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f108 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 213), (1, 215), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cbe) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.exec (n := 217) (ρ' := [(0, 213), (1, 215), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cc2) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 218) (RestInside.exec (n := 218) (ρ' := [(0, 213), (1, 215), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cc6) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f111 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 219), (1, 215), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ccb) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f112 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 219), (1, 221), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cd0) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.exec (n := 223) (ρ' := [(0, 219), (1, 221), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cd4) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 224) (RestInside.exec (n := 224) (ρ' := [(0, 219), (1, 221), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cd8) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f115 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 225), (1, 221), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cdd) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f116 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 225), (1, 227), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ce2) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.exec (n := 229) (ρ' := [(0, 225), (1, 227), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ce6) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 230) (RestInside.exec (n := 230) (ρ' := [(0, 225), (1, 227), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cea) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 231) (RestInside.exec (n := 231) (ρ' := [(0, 225), (1, 227), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109cf0) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109ac0_6 code

theorem rest_l109ac0_4 [Bindings] (code : CodeMap) :
    Rest (n := 174) code lifted (codeRange 0x109ac0 bytes_l109ac0) [(0, 170), (1, 172), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      72 0x109c3a bytes_l109ac0_4 b_l109ac0_4 := by
  have f80 : InstrSpec 0x109c3a [0x88, 0x4C, 0x24, 0x1C] (StorePre 0x109c3a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x109c3a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c3a 4 1 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c3a 4 1 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m8_r8_effect_step 0x109c3a 1 (by decide) (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f81 : InstrSpec 0x109c3e [0x88, 0x44, 0x24, 0x23] (StorePre 0x109c3e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x23)) s (0x109c3e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c3e 4 0 (.sib 4 none 0 (.d8 0x23)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c3e 4 0 (.sib 4 none 0 (.d8 0x23))).toInstrSpec (mov_m8_r8_effect_step 0x109c3e 0 (by decide) (.sib 4 none 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f82 : InstrSpec 0x109c42 [0x0F, 0xB6, 0x44, 0x24, 0x1D] (LoadPre 0x109c42 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x109c42 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c42 5 0 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109c42 5 0 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (movzx_r32_m8_effect_step 0x109c42 0 (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f83 : InstrSpec 0x109c47 [0x0F, 0xB6, 0x4C, 0x24, 0x22] (LoadPre 0x109c47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x109c47 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c47 5 1 (.sib 4 none 0 (.d8 0x22)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109c47 5 1 (.sib 4 none 0 (.d8 0x22))).toInstrSpec (movzx_r32_m8_effect_step 0x109c47 1 (.sib 4 none 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f84 : InstrSpec 0x109c4c [0x88, 0x4C, 0x24, 0x1D] (StorePre 0x109c4c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x109c4c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c4c 4 1 (.sib 4 none 0 (.d8 0x1d)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c4c 4 1 (.sib 4 none 0 (.d8 0x1d))).toInstrSpec (mov_m8_r8_effect_step 0x109c4c 1 (by decide) (.sib 4 none 0 (.d8 0x1d)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f85 : InstrSpec 0x109c50 [0x88, 0x44, 0x24, 0x22] (StorePre 0x109c50 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x109c50 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c50 4 0 (.sib 4 none 0 (.d8 0x22)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c50 4 0 (.sib 4 none 0 (.d8 0x22))).toInstrSpec (mov_m8_r8_effect_step 0x109c50 0 (by decide) (.sib 4 none 0 (.d8 0x22)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f86 : InstrSpec 0x109c54 [0x0F, 0xB6, 0x44, 0x24, 0x1E] (LoadPre 0x109c54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x109c54 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c54 5 0 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109c54 5 0 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (movzx_r32_m8_effect_step 0x109c54 0 (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f87 : InstrSpec 0x109c59 [0x0F, 0xB6, 0x4C, 0x24, 0x21] (LoadPre 0x109c59 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x109c59 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c59 5 1 (.sib 4 none 0 (.d8 0x21)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109c59 5 1 (.sib 4 none 0 (.d8 0x21))).toInstrSpec (movzx_r32_m8_effect_step 0x109c59 1 (.sib 4 none 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f88 : InstrSpec 0x109c5e [0x88, 0x4C, 0x24, 0x1E] (StorePre 0x109c5e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x109c5e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c5e 4 1 (.sib 4 none 0 (.d8 0x1e)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c5e 4 1 (.sib 4 none 0 (.d8 0x1e))).toInstrSpec (mov_m8_r8_effect_step 0x109c5e 1 (by decide) (.sib 4 none 0 (.d8 0x1e)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f89 : InstrSpec 0x109c62 [0x88, 0x44, 0x24, 0x21] (StorePre 0x109c62 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x109c62 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c62 4 0 (.sib 4 none 0 (.d8 0x21)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c62 4 0 (.sib 4 none 0 (.d8 0x21))).toInstrSpec (mov_m8_r8_effect_step 0x109c62 0 (by decide) (.sib 4 none 0 (.d8 0x21)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f90 : InstrSpec 0x109c66 [0x66, 0xC1, 0x44, 0x24, 0x1F, 0x08] (StorePre 0x109c66 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x109c66 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x109c66 6 16 (.sib 4 none 0 (.d8 0x1f)) 8)
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (rolMEffect16_footprint 0x109c66 6 (.sib 4 none 0 (.d8 0x1f)) 8).toInstrSpec (rol_m16_imm8_effect_step 0x109c66 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide) 0x8) (StorePre.of_addr rfl)
  have f91 : InstrSpec 0x109c6c [0x0F, 0xB6, 0x44, 0x24, 0x28] (LoadPre 0x109c6c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109c6c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c6c 5 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109c6c 5 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (movzx_r32_m8_effect_step 0x109c6c 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f92 : InstrSpec 0x109c71 [0x0F, 0xB6, 0x4C, 0x24, 0x37] (LoadPre 0x109c71 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x109c71 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c71 5 1 (.sib 4 none 0 (.d8 0x37)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109c71 5 1 (.sib 4 none 0 (.d8 0x37))).toInstrSpec (movzx_r32_m8_effect_step 0x109c71 1 (.sib 4 none 0 (.d8 0x37)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f93 : InstrSpec 0x109c76 [0x88, 0x4C, 0x24, 0x28] (StorePre 0x109c76 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109c76 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c76 4 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c76 4 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m8_r8_effect_step 0x109c76 1 (by decide) (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f94 : InstrSpec 0x109c7a [0x88, 0x44, 0x24, 0x37] (StorePre 0x109c7a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x109c7a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c7a 4 0 (.sib 4 none 0 (.d8 0x37)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c7a 4 0 (.sib 4 none 0 (.d8 0x37))).toInstrSpec (mov_m8_r8_effect_step 0x109c7a 0 (by decide) (.sib 4 none 0 (.d8 0x37)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f95 : InstrSpec 0x109c7e [0x0F, 0xB6, 0x44, 0x24, 0x29] (LoadPre 0x109c7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x109c7e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c7e 5 0 (.sib 4 none 0 (.d8 0x29)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109c7e 5 0 (.sib 4 none 0 (.d8 0x29))).toInstrSpec (movzx_r32_m8_effect_step 0x109c7e 0 (.sib 4 none 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f96 : InstrSpec 0x109c83 [0x0F, 0xB6, 0x4C, 0x24, 0x36] (LoadPre 0x109c83 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x109c83 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c83 5 1 (.sib 4 none 0 (.d8 0x36)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109c83 5 1 (.sib 4 none 0 (.d8 0x36))).toInstrSpec (movzx_r32_m8_effect_step 0x109c83 1 (.sib 4 none 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f97 : InstrSpec 0x109c88 [0x88, 0x4C, 0x24, 0x29] (StorePre 0x109c88 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x109c88 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c88 4 1 (.sib 4 none 0 (.d8 0x29)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c88 4 1 (.sib 4 none 0 (.d8 0x29))).toInstrSpec (mov_m8_r8_effect_step 0x109c88 1 (by decide) (.sib 4 none 0 (.d8 0x29)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f98 : InstrSpec 0x109c8c [0x88, 0x44, 0x24, 0x36] (StorePre 0x109c8c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x109c8c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c8c 4 0 (.sib 4 none 0 (.d8 0x36)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c8c 4 0 (.sib 4 none 0 (.d8 0x36))).toInstrSpec (mov_m8_r8_effect_step 0x109c8c 0 (by decide) (.sib 4 none 0 (.d8 0x36)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f99 : InstrSpec 0x109c90 [0x0F, 0xB6, 0x44, 0x24, 0x2A] (LoadPre 0x109c90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x109c90 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c90 5 0 (.sib 4 none 0 (.d8 0x2a)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109c90 5 0 (.sib 4 none 0 (.d8 0x2a))).toInstrSpec (movzx_r32_m8_effect_step 0x109c90 0 (.sib 4 none 0 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 174) (RestInside.exec (n := 174) (ρ' := [(0, 170), (1, 172), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c3e) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 175) (RestInside.exec (n := 175) (ρ' := [(0, 170), (1, 172), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c42) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f82 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 176), (1, 172), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c47) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.out (n := 178) f83 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 179) (ρ' := [(0, 176), (1, 178), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c4c) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 180) (RestInside.exec (n := 180) (ρ' := [(0, 176), (1, 178), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c50) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 181) (RestInside.exec (n := 181) (ρ' := [(0, 176), (1, 178), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c54) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 182) (RestInside.out (n := 182) f86 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 183) (ρ' := [(0, 182), (1, 178), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c59) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f87 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 182), (1, 184), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c5e) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.exec (n := 186) (ρ' := [(0, 182), (1, 184), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c62) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 187) (RestInside.exec (n := 187) (ρ' := [(0, 182), (1, 184), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c66) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 188) (RestInside.exec (n := 188) (ρ' := [(0, 182), (1, 184), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c6c) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f91 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 189), (1, 184), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c71) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f92 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 189), (1, 191), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c76) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.exec (n := 193) (ρ' := [(0, 189), (1, 191), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c7a) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 194) (RestInside.exec (n := 194) (ρ' := [(0, 189), (1, 191), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c7e) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f95 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 195), (1, 191), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c83) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f96 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 195), (1, 197), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c88) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.exec (n := 199) (ρ' := [(0, 195), (1, 197), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c8c) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 200) (RestInside.exec (n := 200) (ρ' := [(0, 195), (1, 197), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c90) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f99 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 201), (1, 197), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c95) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109ac0_5 code

theorem rest_l109ac0_3 [Bindings] (code : CodeMap) :
    Rest (n := 144) code lifted (codeRange 0x109ac0 bytes_l109ac0) [(0, 139), (1, 141), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      92 0x109bde bytes_l109ac0_3 b_l109ac0_3 := by
  have f60 : InstrSpec 0x109bde [0x88, 0x44, 0x24, 0x11] (StorePre 0x109bde 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x109bde + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bde 4 0 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109bde 4 0 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (mov_m8_r8_effect_step 0x109bde 0 (by decide) (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f61 : InstrSpec 0x109be2 [0x66, 0xC1, 0x44, 0x24, 0x0F, 0x08] (StorePre 0x109be2 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x109be2 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x109be2 6 16 (.sib 4 none 0 (.d8 0xf)) 8)
      [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [] [.flags, .rip] :=
    (rolMEffect16_footprint 0x109be2 6 (.sib 4 none 0 (.d8 0xf)) 8).toInstrSpec (rol_m16_imm8_effect_step 0x109be2 (.sib 4 none 0 (.d8 0xf)) (by decide) (by decide) (by decide) 0x8) (StorePre.of_addr rfl)
  have f62 : InstrSpec 0x109be8 [0x0F, 0xB6, 0x44, 0x24, 0x18] (LoadPre 0x109be8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109be8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109be8 5 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109be8 5 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (movzx_r32_m8_effect_step 0x109be8 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f63 : InstrSpec 0x109bed [0x0F, 0xB6, 0x4C, 0x24, 0x27] (LoadPre 0x109bed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x109bed + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bed 5 1 (.sib 4 none 0 (.d8 0x27)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109bed 5 1 (.sib 4 none 0 (.d8 0x27))).toInstrSpec (movzx_r32_m8_effect_step 0x109bed 1 (.sib 4 none 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f64 : InstrSpec 0x109bf2 [0x88, 0x4C, 0x24, 0x18] (StorePre 0x109bf2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109bf2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bf2 4 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109bf2 4 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m8_r8_effect_step 0x109bf2 1 (by decide) (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f65 : InstrSpec 0x109bf6 [0x88, 0x44, 0x24, 0x27] (StorePre 0x109bf6 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x109bf6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bf6 4 0 (.sib 4 none 0 (.d8 0x27)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109bf6 4 0 (.sib 4 none 0 (.d8 0x27))).toInstrSpec (mov_m8_r8_effect_step 0x109bf6 0 (by decide) (.sib 4 none 0 (.d8 0x27)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f66 : InstrSpec 0x109bfa [0x0F, 0xB6, 0x44, 0x24, 0x19] (LoadPre 0x109bfa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x109bfa + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bfa 5 0 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109bfa 5 0 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (movzx_r32_m8_effect_step 0x109bfa 0 (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f67 : InstrSpec 0x109bff [0x0F, 0xB6, 0x4C, 0x24, 0x26] (LoadPre 0x109bff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x109bff + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bff 5 1 (.sib 4 none 0 (.d8 0x26)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109bff 5 1 (.sib 4 none 0 (.d8 0x26))).toInstrSpec (movzx_r32_m8_effect_step 0x109bff 1 (.sib 4 none 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f68 : InstrSpec 0x109c04 [0x88, 0x4C, 0x24, 0x19] (StorePre 0x109c04 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x109c04 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c04 4 1 (.sib 4 none 0 (.d8 0x19)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c04 4 1 (.sib 4 none 0 (.d8 0x19))).toInstrSpec (mov_m8_r8_effect_step 0x109c04 1 (by decide) (.sib 4 none 0 (.d8 0x19)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f69 : InstrSpec 0x109c08 [0x88, 0x44, 0x24, 0x26] (StorePre 0x109c08 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x109c08 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c08 4 0 (.sib 4 none 0 (.d8 0x26)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c08 4 0 (.sib 4 none 0 (.d8 0x26))).toInstrSpec (mov_m8_r8_effect_step 0x109c08 0 (by decide) (.sib 4 none 0 (.d8 0x26)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x109c0c [0x0F, 0xB6, 0x44, 0x24, 0x1A] (LoadPre 0x109c0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x109c0c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c0c 5 0 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109c0c 5 0 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (movzx_r32_m8_effect_step 0x109c0c 0 (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f71 : InstrSpec 0x109c11 [0x0F, 0xB6, 0x4C, 0x24, 0x25] (LoadPre 0x109c11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x109c11 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c11 5 1 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109c11 5 1 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (movzx_r32_m8_effect_step 0x109c11 1 (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f72 : InstrSpec 0x109c16 [0x88, 0x4C, 0x24, 0x1A] (StorePre 0x109c16 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x109c16 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c16 4 1 (.sib 4 none 0 (.d8 0x1a)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c16 4 1 (.sib 4 none 0 (.d8 0x1a))).toInstrSpec (mov_m8_r8_effect_step 0x109c16 1 (by decide) (.sib 4 none 0 (.d8 0x1a)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f73 : InstrSpec 0x109c1a [0x88, 0x44, 0x24, 0x25] (StorePre 0x109c1a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x25)) s (0x109c1a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c1a 4 0 (.sib 4 none 0 (.d8 0x25)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c1a 4 0 (.sib 4 none 0 (.d8 0x25))).toInstrSpec (mov_m8_r8_effect_step 0x109c1a 0 (by decide) (.sib 4 none 0 (.d8 0x25)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f74 : InstrSpec 0x109c1e [0x0F, 0xB6, 0x44, 0x24, 0x1B] (LoadPre 0x109c1e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x109c1e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c1e 5 0 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109c1e 5 0 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (movzx_r32_m8_effect_step 0x109c1e 0 (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f75 : InstrSpec 0x109c23 [0x0F, 0xB6, 0x4C, 0x24, 0x24] (LoadPre 0x109c23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x109c23 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c23 5 1 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109c23 5 1 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (movzx_r32_m8_effect_step 0x109c23 1 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f76 : InstrSpec 0x109c28 [0x88, 0x4C, 0x24, 0x1B] (StorePre 0x109c28 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x109c28 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c28 4 1 (.sib 4 none 0 (.d8 0x1b)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c28 4 1 (.sib 4 none 0 (.d8 0x1b))).toInstrSpec (mov_m8_r8_effect_step 0x109c28 1 (by decide) (.sib 4 none 0 (.d8 0x1b)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f77 : InstrSpec 0x109c2c [0x88, 0x44, 0x24, 0x24] (StorePre 0x109c2c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x109c2c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109c2c 4 0 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109c2c 4 0 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_m8_r8_effect_step 0x109c2c 0 (by decide) (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f78 : InstrSpec 0x109c30 [0x0F, 0xB6, 0x44, 0x24, 0x1C] (LoadPre 0x109c30 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x109c30 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c30 5 0 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109c30 5 0 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (movzx_r32_m8_effect_step 0x109c30 0 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f79 : InstrSpec 0x109c35 [0x0F, 0xB6, 0x4C, 0x24, 0x23] (LoadPre 0x109c35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x23)) s (0x109c35 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109c35 5 1 (.sib 4 none 0 (.d8 0x23)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109c35 5 1 (.sib 4 none 0 (.d8 0x23))).toInstrSpec (movzx_r32_m8_effect_step 0x109c35 1 (.sib 4 none 0 (.d8 0x23)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 144) (RestInside.exec (n := 144) (ρ' := [(0, 139), (1, 141), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109be2) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 145) (RestInside.exec (n := 145) (ρ' := [(0, 139), (1, 141), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109be8) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 146) (RestInside.out (n := 146) f62 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 147) (ρ' := [(0, 146), (1, 141), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bed) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 148) (RestInside.out (n := 148) f63 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 149) (ρ' := [(0, 146), (1, 148), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bf2) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 150) (RestInside.exec (n := 150) (ρ' := [(0, 146), (1, 148), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bf6) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 151) (RestInside.exec (n := 151) (ρ' := [(0, 146), (1, 148), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bfa) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f66 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 152), (1, 148), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bff) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f67 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 152), (1, 154), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c04) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.exec (n := 156) (ρ' := [(0, 152), (1, 154), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c08) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 157) (RestInside.exec (n := 157) (ρ' := [(0, 152), (1, 154), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c0c) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f70 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 158), (1, 154), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c11) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f71 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 158), (1, 160), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c16) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.exec (n := 162) (ρ' := [(0, 158), (1, 160), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c1a) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 163) (RestInside.exec (n := 163) (ρ' := [(0, 158), (1, 160), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c1e) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f74 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 164), (1, 160), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c23) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f75 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 164), (1, 166), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c28) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.exec (n := 168) (ρ' := [(0, 164), (1, 166), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c2c) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 169) (RestInside.exec (n := 169) (ρ' := [(0, 164), (1, 166), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c30) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f78 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 170), (1, 166), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c35) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f79 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 170), (1, 172), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109c3a) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l109ac0_4 code

theorem rest_l109ac0_2 [Bindings] (code : CodeMap) :
    Rest (n := 114) code lifted (codeRange 0x109ac0 bytes_l109ac0) [(0, 109), (1, 111), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      112 0x109b84 bytes_l109ac0_2 b_l109ac0_2 := by
  have f40 : InstrSpec 0x109b84 [0x88, 0x44, 0x24, 0x16] (StorePre 0x109b84 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x109b84 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b84 4 0 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109b84 4 0 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (mov_m8_r8_effect_step 0x109b84 0 (by decide) (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f41 : InstrSpec 0x109b88 [0x0F, 0xB6, 0x44, 0x24, 0x0A] (LoadPre 0x109b88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x109b88 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b88 5 0 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109b88 5 0 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m8_effect_step 0x109b88 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f42 : InstrSpec 0x109b8d [0x0F, 0xB6, 0x4C, 0x24, 0x15] (LoadPre 0x109b8d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x109b8d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b8d 5 1 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109b8d 5 1 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (movzx_r32_m8_effect_step 0x109b8d 1 (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f43 : InstrSpec 0x109b92 [0x88, 0x4C, 0x24, 0x0A] (StorePre 0x109b92 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x109b92 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b92 4 1 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109b92 4 1 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m8_r8_effect_step 0x109b92 1 (by decide) (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f44 : InstrSpec 0x109b96 [0x88, 0x44, 0x24, 0x15] (StorePre 0x109b96 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x109b96 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b96 4 0 (.sib 4 none 0 (.d8 0x15)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109b96 4 0 (.sib 4 none 0 (.d8 0x15))).toInstrSpec (mov_m8_r8_effect_step 0x109b96 0 (by decide) (.sib 4 none 0 (.d8 0x15)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f45 : InstrSpec 0x109b9a [0x0F, 0xB6, 0x44, 0x24, 0x0B] (LoadPre 0x109b9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x109b9a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b9a 5 0 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109b9a 5 0 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (movzx_r32_m8_effect_step 0x109b9a 0 (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f46 : InstrSpec 0x109b9f [0x0F, 0xB6, 0x4C, 0x24, 0x14] (LoadPre 0x109b9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x109b9f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b9f 5 1 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109b9f 5 1 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (movzx_r32_m8_effect_step 0x109b9f 1 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f47 : InstrSpec 0x109ba4 [0x88, 0x4C, 0x24, 0x0B] (StorePre 0x109ba4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x109ba4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109ba4 4 1 (.sib 4 none 0 (.d8 0xb)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109ba4 4 1 (.sib 4 none 0 (.d8 0xb))).toInstrSpec (mov_m8_r8_effect_step 0x109ba4 1 (by decide) (.sib 4 none 0 (.d8 0xb)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x109ba8 [0x88, 0x44, 0x24, 0x14] (StorePre 0x109ba8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x109ba8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109ba8 4 0 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109ba8 4 0 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m8_r8_effect_step 0x109ba8 0 (by decide) (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f49 : InstrSpec 0x109bac [0x0F, 0xB6, 0x44, 0x24, 0x0C] (LoadPre 0x109bac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x109bac + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bac 5 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109bac 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m8_effect_step 0x109bac 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f50 : InstrSpec 0x109bb1 [0x0F, 0xB6, 0x4C, 0x24, 0x13] (LoadPre 0x109bb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x109bb1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bb1 5 1 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109bb1 5 1 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (movzx_r32_m8_effect_step 0x109bb1 1 (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f51 : InstrSpec 0x109bb6 [0x88, 0x4C, 0x24, 0x0C] (StorePre 0x109bb6 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x109bb6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bb6 4 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109bb6 4 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m8_r8_effect_step 0x109bb6 1 (by decide) (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f52 : InstrSpec 0x109bba [0x88, 0x44, 0x24, 0x13] (StorePre 0x109bba 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x109bba + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bba 4 0 (.sib 4 none 0 (.d8 0x13)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109bba 4 0 (.sib 4 none 0 (.d8 0x13))).toInstrSpec (mov_m8_r8_effect_step 0x109bba 0 (by decide) (.sib 4 none 0 (.d8 0x13)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f53 : InstrSpec 0x109bbe [0x0F, 0xB6, 0x44, 0x24, 0x0D] (LoadPre 0x109bbe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x109bbe + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bbe 5 0 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109bbe 5 0 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (movzx_r32_m8_effect_step 0x109bbe 0 (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x109bc3 [0x0F, 0xB6, 0x4C, 0x24, 0x12] (LoadPre 0x109bc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x109bc3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bc3 5 1 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109bc3 5 1 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (movzx_r32_m8_effect_step 0x109bc3 1 (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f55 : InstrSpec 0x109bc8 [0x88, 0x4C, 0x24, 0x0D] (StorePre 0x109bc8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x109bc8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bc8 4 1 (.sib 4 none 0 (.d8 0xd)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109bc8 4 1 (.sib 4 none 0 (.d8 0xd))).toInstrSpec (mov_m8_r8_effect_step 0x109bc8 1 (by decide) (.sib 4 none 0 (.d8 0xd)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x109bcc [0x88, 0x44, 0x24, 0x12] (StorePre 0x109bcc 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x109bcc + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bcc 4 0 (.sib 4 none 0 (.d8 0x12)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109bcc 4 0 (.sib 4 none 0 (.d8 0x12))).toInstrSpec (mov_m8_r8_effect_step 0x109bcc 0 (by decide) (.sib 4 none 0 (.d8 0x12)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f57 : InstrSpec 0x109bd0 [0x0F, 0xB6, 0x44, 0x24, 0x0E] (LoadPre 0x109bd0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x109bd0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bd0 5 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109bd0 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m8_effect_step 0x109bd0 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f58 : InstrSpec 0x109bd5 [0x0F, 0xB6, 0x4C, 0x24, 0x11] (LoadPre 0x109bd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x109bd5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109bd5 5 1 (.sib 4 none 0 (.d8 0x11)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109bd5 5 1 (.sib 4 none 0 (.d8 0x11))).toInstrSpec (movzx_r32_m8_effect_step 0x109bd5 1 (.sib 4 none 0 (.d8 0x11)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x109bda [0x88, 0x4C, 0x24, 0x0E] (StorePre 0x109bda 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x109bda + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109bda 4 1 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109bda 4 1 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m8_r8_effect_step 0x109bda 1 (by decide) (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 109), (1, 111), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b88) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f41 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 115), (1, 111), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b8d) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f42 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 115), (1, 117), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b92) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.exec (n := 119) (ρ' := [(0, 115), (1, 117), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b96) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 120) (RestInside.exec (n := 120) (ρ' := [(0, 115), (1, 117), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b9a) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 121), (1, 117), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b9f) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f46 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 121), (1, 123), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ba4) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.exec (n := 125) (ρ' := [(0, 121), (1, 123), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ba8) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 126) (RestInside.exec (n := 126) (ρ' := [(0, 121), (1, 123), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bac) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f49 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 127), (1, 123), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bb1) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f50 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 127), (1, 129), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bb6) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.exec (n := 131) (ρ' := [(0, 127), (1, 129), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bba) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 132) (RestInside.exec (n := 132) (ρ' := [(0, 127), (1, 129), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bbe) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f53 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 133), (1, 129), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bc3) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f54 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 133), (1, 135), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bc8) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.exec (n := 137) (ρ' := [(0, 133), (1, 135), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bcc) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 138) (RestInside.exec (n := 138) (ρ' := [(0, 133), (1, 135), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bd0) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f57 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 139), (1, 135), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bd5) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 139), (1, 141), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bda) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.exec (n := 143) (ρ' := [(0, 139), (1, 141), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109bde) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109ac0_3 code

theorem rest_l109ac0_1 [Bindings] (code : CodeMap) :
    Rest (n := 84) code lifted (codeRange 0x109ac0 bytes_l109ac0) [(0, 79), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      132 0x109b20 bytes_l109ac0_1 b_l109ac0_1 := by
  have f20 : InstrSpec 0x109b20 [0x48, 0x89, 0x4C, 0x24, 0x10] (StorePre 0x109b20 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109b20 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b20 1 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b20 1 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x109b20 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x109b25 [0x48, 0x8B, 0x44, 0x24, 0x58] (LoadPre 0x109b25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x109b25 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b25 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109b25 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_r64_m64_effect_step 0x109b25 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x109b2a [0x48, 0x89, 0x44, 0x24, 0x18] (StorePre 0x109b2a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109b2a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b2a 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b2a 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x109b2a 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x109b2f [0x48, 0x8B, 0x44, 0x24, 0x60] (LoadPre 0x109b2f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x109b2f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b2f 0 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109b2f 0 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x109b2f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f24 : InstrSpec 0x109b34 [0x48, 0x89, 0x44, 0x24, 0x20] (StorePre 0x109b34 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109b34 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b34 0 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b34 0 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x109b34 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f25 : InstrSpec 0x109b39 [0x48, 0x8B, 0x44, 0x24, 0x68] (LoadPre 0x109b39 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109b39 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b39 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109b39 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_r64_m64_effect_step 0x109b39 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f26 : InstrSpec 0x109b3e [0x48, 0x89, 0x44, 0x24, 0x28] (StorePre 0x109b3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109b3e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b3e 0 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b3e 0 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x109b3e 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f27 : InstrSpec 0x109b43 [0x48, 0x8B, 0x44, 0x24, 0x70] (LoadPre 0x109b43 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x109b43 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b43 0 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109b43 0 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_r64_m64_effect_step 0x109b43 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f28 : InstrSpec 0x109b48 [0x48, 0x89, 0x44, 0x24, 0x30] (StorePre 0x109b48 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109b48 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b48 0 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b48 0 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x109b48 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f29 : InstrSpec 0x109b4d [0x48, 0x8B, 0x44, 0x24, 0x78] (LoadPre 0x109b4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109b4d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b4d 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109b4d 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r64_m64_effect_step 0x109b4d 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f30 : InstrSpec 0x109b52 [0x48, 0x89, 0x44, 0x24, 0x38] (StorePre 0x109b52 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109b52 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b52 0 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b52 0 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x109b52 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f31 : InstrSpec 0x109b57 [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00] (LoadPre 0x109b57 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109b57 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109b57 0 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109b57 0 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_r64_m64_effect_step 0x109b57 0x48 (by decide) 0 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f32 : InstrSpec 0x109b5f [0x48, 0x89, 0x44, 0x24, 0x40] (StorePre 0x109b5f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109b5f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b5f 0 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b5f 0 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x109b5f 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x109b64 [0x0F, 0xB6, 0x44, 0x24, 0x08] (LoadPre 0x109b64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109b64 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b64 5 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109b64 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m8_effect_step 0x109b64 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f34 : InstrSpec 0x109b69 [0x0F, 0xB6, 0x4C, 0x24, 0x17] (LoadPre 0x109b69 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x109b69 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b69 5 1 (.sib 4 none 0 (.d8 0x17)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109b69 5 1 (.sib 4 none 0 (.d8 0x17))).toInstrSpec (movzx_r32_m8_effect_step 0x109b69 1 (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x109b6e [0x88, 0x4C, 0x24, 0x08] (StorePre 0x109b6e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109b6e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b6e 4 1 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109b6e 4 1 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m8_r8_effect_step 0x109b6e 1 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x109b72 [0x88, 0x44, 0x24, 0x17] (StorePre 0x109b72 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x109b72 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b72 4 0 (.sib 4 none 0 (.d8 0x17)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109b72 4 0 (.sib 4 none 0 (.d8 0x17))).toInstrSpec (mov_m8_r8_effect_step 0x109b72 0 (by decide) (.sib 4 none 0 (.d8 0x17)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f37 : InstrSpec 0x109b76 [0x0F, 0xB6, 0x44, 0x24, 0x09] (LoadPre 0x109b76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x109b76 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b76 5 0 (.sib 4 none 0 (.d8 0x9)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M8Effect_footprint 0x109b76 5 0 (.sib 4 none 0 (.d8 0x9))).toInstrSpec (movzx_r32_m8_effect_step 0x109b76 0 (.sib 4 none 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f38 : InstrSpec 0x109b7b [0x0F, 0xB6, 0x4C, 0x24, 0x16] (LoadPre 0x109b7b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x109b7b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109b7b 5 1 (.sib 4 none 0 (.d8 0x16)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M8Effect_footprint 0x109b7b 5 1 (.sib 4 none 0 (.d8 0x16))).toInstrSpec (movzx_r32_m8_effect_step 0x109b7b 1 (.sib 4 none 0 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f39 : InstrSpec 0x109b80 [0x88, 0x4C, 0x24, 0x09] (StorePre 0x109b80 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x109b80 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109b80 4 1 (.sib 4 none 0 (.d8 0x9)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM8R8Effect_footprint 0x109b80 4 1 (.sib 4 none 0 (.d8 0x9))).toInstrSpec (mov_m8_r8_effect_step 0x109b80 1 (by decide) (.sib 4 none 0 (.d8 0x9)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 84) (RestInside.exec (n := 84) (ρ' := [(0, 79), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b25) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b2a) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(0, 85), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b2f) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f23 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b34) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.exec (n := 90) (ρ' := [(0, 88), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b39) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f25 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 91), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b3e) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.exec (n := 93) (ρ' := [(0, 91), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b43) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 94) (RestInside.out (n := 94) f27 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 95) (ρ' := [(0, 94), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b48) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 96) (RestInside.exec (n := 96) (ρ' := [(0, 94), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b4d) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 97), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b52) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.exec (n := 99) (ρ' := [(0, 97), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b57) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f31 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 100), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b5f) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.exec (n := 102) (ρ' := [(0, 100), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b64) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f33 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 103), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b69) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f34 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 103), (1, 105), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b6e) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.exec (n := 107) (ρ' := [(0, 103), (1, 105), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b72) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 108) (RestInside.exec (n := 108) (ρ' := [(0, 103), (1, 105), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b76) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 109), (1, 105), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b7b) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f38 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 109), (1, 111), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b80) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.exec (n := 113) (ρ' := [(0, 109), (1, 111), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b84) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109ac0_2 code

theorem rest_l109ac0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109ac0 bytes_l109ac0) (entryMap (live .l109ac0))
      152 0x109ac0 bytes_l109ac0 b_l109ac0 := by
  have f0 : InstrSpec 0x109ac0 [0x48, 0x81, 0xEC, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109ac0) (subR64Imm32Effect 0x109ac0 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm32Effect_footprint 0x109ac0 4 0x88).toInstrSpec (sub_r64_imm32_effect_step 0x109ac0 0x48 0xec 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109ac7 [0x48, 0x8B, 0x06] (LoadPre 0x109ac7 (fun s => AddrMode.addr (.base 6 .none) s (0x109ac7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109ac7 0 (.base 6 .none))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109ac7 0 (.base 6 .none)).toInstrSpec (mov_r64_m64_effect_step 0x109ac7 0x48 (by decide) 0 (.base 6 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x109aca [0x48, 0x8B, 0x4E, 0x08] (LoadPre 0x109aca (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109aca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aca 1 (.base 6 (.d8 0x8)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109aca 1 (.base 6 (.d8 0x8))).toInstrSpec (mov_r64_m64_effect_step 0x109aca 0x48 (by decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x109ace [0x48, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x109ace 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109ace + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ace 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109ace 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m64_r64_effect_step 0x109ace 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x109ad3 [0x48, 0x89, 0x44, 0x24, 0x48] (StorePre 0x109ad3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109ad3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ad3 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109ad3 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_m64_r64_effect_step 0x109ad3 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x109ad8 [0x48, 0x8B, 0x46, 0x10] (LoadPre 0x109ad8 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109ad8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109ad8 0 (.base 6 (.d8 0x10)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109ad8 0 (.base 6 (.d8 0x10))).toInstrSpec (mov_r64_m64_effect_step 0x109ad8 0x48 (by decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x109adc [0x48, 0x8B, 0x4E, 0x18] (LoadPre 0x109adc (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109adc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109adc 1 (.base 6 (.d8 0x18)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109adc 1 (.base 6 (.d8 0x18))).toInstrSpec (mov_r64_m64_effect_step 0x109adc 0x48 (by decide) 1 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x109ae0 [0x48, 0x89, 0x4C, 0x24, 0x60] (StorePre 0x109ae0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x109ae0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ae0 1 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109ae0 1 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m64_r64_effect_step 0x109ae0 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x109ae5 [0x48, 0x89, 0x44, 0x24, 0x58] (StorePre 0x109ae5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x109ae5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ae5 0 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109ae5 0 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x109ae5 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x109aea [0x48, 0x8B, 0x46, 0x20] (LoadPre 0x109aea (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x109aea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aea 0 (.base 6 (.d8 0x20)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109aea 0 (.base 6 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x109aea 0x48 (by decide) 0 (.base 6 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x109aee [0x48, 0x8B, 0x4E, 0x28] (LoadPre 0x109aee (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x109aee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aee 1 (.base 6 (.d8 0x28)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109aee 1 (.base 6 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x109aee 0x48 (by decide) 1 (.base 6 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x109af2 [0x48, 0x89, 0x4C, 0x24, 0x70] (StorePre 0x109af2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x109af2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109af2 1 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109af2 1 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m64_r64_effect_step 0x109af2 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x109af7 [0x48, 0x89, 0x44, 0x24, 0x68] (StorePre 0x109af7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109af7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109af7 0 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109af7 0 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m64_r64_effect_step 0x109af7 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x109afc [0x48, 0x8B, 0x46, 0x30] (LoadPre 0x109afc (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x109afc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109afc 0 (.base 6 (.d8 0x30)))
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109afc 0 (.base 6 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x109afc 0x48 (by decide) 0 (.base 6 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x109b00 [0x48, 0x8B, 0x4E, 0x38] (LoadPre 0x109b00 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x109b00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109b00 1 (.base 6 (.d8 0x38)))
      [.gpr 6] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109b00 1 (.base 6 (.d8 0x38))).toInstrSpec (mov_r64_m64_effect_step 0x109b00 0x48 (by decide) 1 (.base 6 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x109b04 [0x48, 0x89, 0x44, 0x24, 0x78] (StorePre 0x109b04 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109b04 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b04 0 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b04 0 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m64_r64_effect_step 0x109b04 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x109b09 [0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00] (StorePre 0x109b09 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109b09 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109b09 1 (.sib 4 none 0 (.d32 0x80)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b09 1 (.sib 4 none 0 (.d32 0x80))).toInstrSpec (mov_m64_r64_effect_step 0x109b09 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0x80)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x109b11 [0x48, 0x8B, 0x44, 0x24, 0x48] (LoadPre 0x109b11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109b11 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b11 0 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR64M64Effect_footprint 0x109b11 0 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x109b11 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x109b16 [0x48, 0x8B, 0x4C, 0x24, 0x50] (LoadPre 0x109b16 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109b16 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b16 1 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x109b16 1 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_r64_m64_effect_step 0x109b16 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x109b1b [0x48, 0x89, 0x44, 0x24, 0x08] (StorePre 0x109b1b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109b1b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109b1b 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x109b1b 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x109b1b 0x48 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ac7) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aca) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ace) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ad3) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 55), (1, 57), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ad8) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 57), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109adc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ae0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ae5) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 61), (1, 63), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aea) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 63), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109aee) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 69), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109af2) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 67), (1, 69), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109af7) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 69), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109afc) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 69), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b00) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 73), (1, 75), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b04) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(0, 73), (1, 75), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b09) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 73), (1, 75), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b11) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 79), (1, 75), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b16) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 79), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b1b) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.exec (n := 83) (ρ' := [(0, 79), (1, 81), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109b20) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l109ac0_1 code

theorem block_l109ac0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109ac0 :=
  Rest.liftedBlock (rest_l109ac0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109ac0 x hx)

theorem rest_l109d81 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x109d81 bytes_l109d81) (entryMap (live .l109d81))
      2 0x109d81 bytes_l109d81 b_l109d81 := by
  have f0 : InstrSpec 0x109d81 [0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x109d81) (addR64Imm32Effect 0x109d81 4 0x88)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm32Effect_footprint 0x109d81 4 0x88).toInstrSpec (add_r64_imm32_effect_step 0x109d81 0x48 0xc4 0x88 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x109d88 [0xC3] (RetPre 0x109d88) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x109d88).toInstrSpec (ret_effect_step 0x109d88) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d88) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 56) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) f1 (by decide) rfl rfl rfl (by decide)

theorem block_l109d81 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l109d81 :=
  Rest.liftedBlock (rest_l109d81 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l109d81 x hx)

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

theorem_by block_l109ac0_eval :
    program.runBlock (dialect code) ⟨.l109ac0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l109d81_eval :
    program.runBlock (dialect code) ⟨.l109d81, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
