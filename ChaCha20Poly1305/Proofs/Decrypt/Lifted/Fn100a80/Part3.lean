import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Program
import X86Proofs.Instructions.Branch.Triple
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

theorem rest_l101036_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x101036 bytes_l101036) [(0, 0), (1, 77), (2, 79), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]
      1 0x1010ad bytes_l101036_1 b_l101036_1 := by
  exact Rest.jcc (n := 85) (jcc_rel32_effect_step 0x1010ad 5 0xfffffbbd) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l101036 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101036 bytes_l101036) (entryMap (live .l101036))
      21 0x101036 bytes_l101036 b_l101036 := by
  have f0 : InstrSpec 0x101036 [0x41, 0xFF, 0xC4] (fun s => s.RIP = 0x101036) (incR32Effect 0x101036 3 12)
      [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 12, .flags, .rip] :=
    (incR32Effect_footprint 0x101036 3 12).toInstrSpec (inc_r32_rex_effect_step 0x101036 0x41 0xc4 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x101039 [0x48, 0xFF, 0xC7] (fun s => s.RIP = 0x101039) (incR64Effect 0x101039 7)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (incR64Effect_footprint 0x101039 7).toInstrSpec (inc_r64_effect_step 0x101039 0x48 0xc7 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10103c [0x48, 0x8B, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00] (LoadPre 0x10103c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10103c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10103c 1 (.sib 4 none 0 (.d32 0xe8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10103c 1 (.sib 4 none 0 (.d32 0xe8))).toInstrSpec (mov_r64_m64_effect_step 0x10103c 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x101044 [0x48, 0x8B, 0x74, 0x24, 0x60] (LoadPre 0x101044 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x101044 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101044 6 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR64M64Effect_footprint 0x101044 6 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_r64_m64_effect_step 0x101044 0x48 (by decide) 6 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x101049 [0x48, 0x89, 0x4C, 0x06, 0x38] (StorePre 0x101049 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x38)) s (0x101049 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101049 1 (.sib 6 (some 0) 0 (.d8 0x38)))
      [.gpr 1, .gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x101049 1 (.sib 6 (some 0) 0 (.d8 0x38))).toInstrSpec (mov_m64_r64_effect_step 0x101049 0x48 (by decide) 1 (.sib 6 (some 0) 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x10104e [0x48, 0x8B, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00] (LoadPre 0x10104e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10104e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10104e 1 (.sib 4 none 0 (.d32 0xe0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10104e 1 (.sib 4 none 0 (.d32 0xe0))).toInstrSpec (mov_r64_m64_effect_step 0x10104e 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101056 [0x48, 0x89, 0x4C, 0x06, 0x30] (StorePre 0x101056 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x30)) s (0x101056 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101056 1 (.sib 6 (some 0) 0 (.d8 0x30)))
      [.gpr 1, .gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x101056 1 (.sib 6 (some 0) 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x101056 0x48 (by decide) 1 (.sib 6 (some 0) 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10105b [0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00] (LoadPre 0x10105b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10105b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10105b 1 (.sib 4 none 0 (.d32 0xd8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10105b 1 (.sib 4 none 0 (.d32 0xd8))).toInstrSpec (mov_r64_m64_effect_step 0x10105b 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x101063 [0x48, 0x89, 0x4C, 0x06, 0x28] (StorePre 0x101063 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x28)) s (0x101063 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101063 1 (.sib 6 (some 0) 0 (.d8 0x28)))
      [.gpr 1, .gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x101063 1 (.sib 6 (some 0) 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x101063 0x48 (by decide) 1 (.sib 6 (some 0) 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101068 [0x48, 0x8B, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00] (LoadPre 0x101068 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x101068 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101068 1 (.sib 4 none 0 (.d32 0xd0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101068 1 (.sib 4 none 0 (.d32 0xd0))).toInstrSpec (mov_r64_m64_effect_step 0x101068 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x101070 [0x48, 0x89, 0x4C, 0x06, 0x20] (StorePre 0x101070 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x20)) s (0x101070 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101070 1 (.sib 6 (some 0) 0 (.d8 0x20)))
      [.gpr 1, .gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x101070 1 (.sib 6 (some 0) 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x101070 0x48 (by decide) 1 (.sib 6 (some 0) 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x101075 [0x48, 0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00] (LoadPre 0x101075 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x101075 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101075 1 (.sib 4 none 0 (.d32 0xc8)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101075 1 (.sib 4 none 0 (.d32 0xc8))).toInstrSpec (mov_r64_m64_effect_step 0x101075 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10107d [0x48, 0x89, 0x4C, 0x06, 0x18] (StorePre 0x10107d 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x18)) s (0x10107d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10107d 1 (.sib 6 (some 0) 0 (.d8 0x18)))
      [.gpr 1, .gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10107d 1 (.sib 6 (some 0) 0 (.d8 0x18))).toInstrSpec (mov_m64_r64_effect_step 0x10107d 0x48 (by decide) 1 (.sib 6 (some 0) 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101082 [0x48, 0x8B, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00] (LoadPre 0x101082 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x101082 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101082 1 (.sib 4 none 0 (.d32 0xc0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x101082 1 (.sib 4 none 0 (.d32 0xc0))).toInstrSpec (mov_r64_m64_effect_step 0x101082 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x10108a [0x48, 0x89, 0x4C, 0x06, 0x10] (StorePre 0x10108a 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x10)) s (0x10108a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10108a 1 (.sib 6 (some 0) 0 (.d8 0x10)))
      [.gpr 1, .gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10108a 1 (.sib 6 (some 0) 0 (.d8 0x10))).toInstrSpec (mov_m64_r64_effect_step 0x10108a 0x48 (by decide) 1 (.sib 6 (some 0) 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10108f [0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00] (LoadPre 0x10108f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10108f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10108f 1 (.sib 4 none 0 (.d32 0xb0)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x10108f 1 (.sib 4 none 0 (.d32 0xb0))).toInstrSpec (mov_r64_m64_effect_step 0x10108f 0x48 (by decide) 1 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x101097 [0x48, 0x8B, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00] (LoadPre 0x101097 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x101097 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101097 2 (.sib 4 none 0 (.d32 0xb8)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR64M64Effect_footprint 0x101097 2 (.sib 4 none 0 (.d32 0xb8))).toInstrSpec (mov_r64_m64_effect_step 0x101097 0x48 (by decide) 2 (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10109f [0x48, 0x89, 0x54, 0x06, 0x08] (StorePre 0x10109f 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x8)) s (0x10109f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10109f 2 (.sib 6 (some 0) 0 (.d8 0x8)))
      [.gpr 2, .gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x10109f 2 (.sib 6 (some 0) 0 (.d8 0x8))).toInstrSpec (mov_m64_r64_effect_step 0x10109f 0x48 (by decide) 2 (.sib 6 (some 0) 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x1010a4 [0x48, 0x89, 0x0C, 0x06] (StorePre 0x1010a4 4 (fun s => AddrMode.addr (.sib 6 (some 0) 0 .none) s (0x1010a4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1010a4 1 (.sib 6 (some 0) 0 .none))
      [.gpr 1, .gpr 6, .gpr 0] [] [.rip] :=
    (movM64R64Effect_footprint 0x1010a4 1 (.sib 6 (some 0) 0 .none)).toInstrSpec (mov_m64_r64_effect_step 0x1010a4 0x48 (by decide) 1 (.sib 6 (some 0) 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f19 : InstrSpec 0x1010a8 [0x48, 0x39, 0x7C, 0x24, 0x50] (LoadPre 0x1010a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1010a8 + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x1010a8 5 64 7 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 7, .gpr 4] [] [.flags, .rip] :=
    (cmpMREffect64_footprint 0x1010a8 5 7 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (cmp_m64_r64_effect_step 0x1010a8 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101039) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10103c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (4, 4), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101044) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101049) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 57), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10104e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 62), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101056) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 62), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10105b) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 65), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101063) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 65), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101068) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 68), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101070) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 68), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101075) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 71), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10107d) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 71), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101082) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 74), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10108a) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 74), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10108f) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f15 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 77), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101097) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 77), (2, 79), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10109f) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 77), (2, 79), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010a4) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 77), (2, 79), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010a8) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 77), (2, 79), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010ad) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l101036_1 code

theorem block_l101036 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101036 :=
  Rest.liftedBlock (rest_l101036 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101036 x hx)

theorem rest_l1010b3 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1010b3 bytes_l1010b3) (entryMap (live .l1010b3))
      4 0x1010b3 bytes_l1010b3 b_l1010b3 := by
  have f0 : InstrSpec 0x1010b3 [0x48, 0x8B, 0x7C, 0x24, 0x48] (LoadPre 0x1010b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1010b3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010b3 7 (.sib 4 none 0 (.d8 0x48)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64M64Effect_footprint 0x1010b3 7 (.sib 4 none 0 (.d8 0x48))).toInstrSpec (mov_r64_m64_effect_step 0x1010b3 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1010b8 [0x44, 0x89, 0x67, 0x30] (StorePre 0x1010b8 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x1010b8 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1010b8 12 (.base 7 (.d8 0x30)))
      [.gpr 12, .gpr 7] [] [.rip] :=
    (movM32R32Effect_footprint 0x1010b8 12 (.base 7 (.d8 0x30))).toInstrSpec (mov_m32_r32_effect_step 0x1010b8 0x44 (by decide) 4 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1010bc [0x4C, 0x8B, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x1010bc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1010bc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1010bc 11 (.sib 4 none 0 (.d32 0xa8)))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR64M64Effect_footprint 0x1010bc 11 (.sib 4 none 0 (.d32 0xa8))).toInstrSpec (mov_r64_m64_effect_step 0x1010bc 0x4c (by decide) 3 (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1010c4 [0x4C, 0x8B, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x1010c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1010c4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1010c4 15 (.sib 4 none 0 (.d32 0xa0)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64M64Effect_footprint 0x1010c4 15 (.sib 4 none 0 (.d32 0xa0))).toInstrSpec (mov_r64_m64_effect_step 0x1010c4 0x4c (by decide) 7 (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (9, 9), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010b8) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (9, 9), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010bc) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (9, 9), (11, 56), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010c4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (9, 9), (11, 56), (12, 12), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010cc) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 60) (by decide) rfl

theorem block_l1010b3 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1010b3 :=
  Rest.liftedBlock (rest_l1010b3 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1010b3 x hx)

theorem rest_l1010cc [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1010cc bytes_l1010cc) (entryMap (live .l1010cc))
      2 0x1010cc bytes_l1010cc b_l1010cc := by
  have f0 : InstrSpec 0x1010cc [0x4D, 0x85, 0xFF] (fun s => s.RIP = 0x1010cc) (testR64R64Effect 0x1010cc 15 15)
      [.gpr 15, .gpr 15] [] [.flags, .rip] :=
    (testR64R64Effect_footprint 0x1010cc 15 15).toInstrSpec (test_r64_r64_effect_step 0x1010cc 0x4d 0xff (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (11, 11), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010cf) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 55) (jcc_rel32_effect_step 0x1010cf 4 0x3d3) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem block_l1010cc [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1010cc :=
  Rest.liftedBlock (rest_l1010cc code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1010cc x hx)

theorem rest_l1010d5 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1010d5 bytes_l1010d5) (entryMap (live .l1010d5))
      20 0x1010d5 bytes_l1010d5 b_l1010d5 := by
  have f0 : InstrSpec 0x1010d5 [0x49, 0x83, 0xE3, 0xC0] (fun s => s.RIP = 0x1010d5) (andR64Imm8Effect 0x1010d5 11 0xc0)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR64Imm8Effect_footprint 0x1010d5 11 0xc0).toInstrSpec (and_r64_imm8_effect_step 0x1010d5 0x49 0xe3 0xc0 (by decide) (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1010d9 [0x4C, 0x89, 0x5C, 0x24, 0x40] (StorePre 0x1010d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1010d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010d9 11 (.sib 4 none 0 (.d8 0x40)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x1010d9 11 (.sib 4 none 0 (.d8 0x40))).toInstrSpec (mov_m64_r64_effect_step 0x1010d9 0x4c (by decide) 3 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x1010de [0x8B, 0x1F] (LoadPre 0x1010de (fun s => AddrMode.addr (.base 7 .none) s (0x1010de + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x1010de 3 (.base 7 .none))
      [.gpr 7] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x1010de 3 (.base 7 .none)).toInstrSpec (mov_r32_m32_low_effect_step 0x1010de 3 (.base 7 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1010e0 [0x44, 0x8B, 0x6F, 0x04] (LoadPre 0x1010e0 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x1010e0 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1010e0 13 (.base 7 (.d8 0x4)))
      [.gpr 7] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x1010e0 13 (.base 7 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x1010e0 0x44 (by decide) 5 (.base 7 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x1010e4 [0x8B, 0x77, 0x08] (LoadPre 0x1010e4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1010e4 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1010e4 6 (.base 7 (.d8 0x8)))
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x1010e4 6 (.base 7 (.d8 0x8))).toInstrSpec (mov_r32_m32_low_effect_step 0x1010e4 6 (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1010e7 [0x8B, 0x47, 0x0C] (LoadPre 0x1010e7 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x1010e7 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1010e7 0 (.base 7 (.d8 0xc)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1010e7 0 (.base 7 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x1010e7 0 (.base 7 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1010ea [0x89, 0x44, 0x24, 0x0C] (StorePre 0x1010ea 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1010ea + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1010ea 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1010ea 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m32_r32_low_effect_step 0x1010ea 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x1010ee [0x44, 0x8B, 0x4F, 0x10] (LoadPre 0x1010ee (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1010ee + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1010ee 9 (.base 7 (.d8 0x10)))
      [.gpr 7] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x1010ee 9 (.base 7 (.d8 0x10))).toInstrSpec (mov_r32_m32_effect_step 0x1010ee 0x44 (by decide) 1 (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1010f2 [0x8B, 0x6F, 0x14] (LoadPre 0x1010f2 (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x1010f2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1010f2 5 (.base 7 (.d8 0x14)))
      [.gpr 7] [] [.reg 5, .rip] :=
    (movR32M32LowEffect_footprint 0x1010f2 5 (.base 7 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x1010f2 5 (.base 7 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1010f5 [0x44, 0x8B, 0x7F, 0x18] (LoadPre 0x1010f5 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1010f5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1010f5 15 (.base 7 (.d8 0x18)))
      [.gpr 7] [] [.reg 15, .rip] :=
    (movR32M32Effect_footprint 0x1010f5 15 (.base 7 (.d8 0x18))).toInstrSpec (mov_r32_m32_effect_step 0x1010f5 0x44 (by decide) 7 (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1010f9 [0x8B, 0x47, 0x1C] (LoadPre 0x1010f9 (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x1010f9 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1010f9 0 (.base 7 (.d8 0x1c)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x1010f9 0 (.base 7 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x1010f9 0 (.base 7 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1010fc [0x89, 0x44, 0x24, 0x10] (StorePre 0x1010fc 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1010fc + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1010fc 0 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1010fc 0 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_m32_r32_low_effect_step 0x1010fc 0 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x101100 [0x8B, 0x47, 0x20] (LoadPre 0x101100 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x101100 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101100 0 (.base 7 (.d8 0x20)))
      [.gpr 7] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x101100 0 (.base 7 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x101100 0 (.base 7 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x101103 [0x44, 0x8B, 0x57, 0x24] (LoadPre 0x101103 (fun s => AddrMode.addr (.base 7 (.d8 0x24)) s (0x101103 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101103 10 (.base 7 (.d8 0x24)))
      [.gpr 7] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x101103 10 (.base 7 (.d8 0x24))).toInstrSpec (mov_r32_m32_effect_step 0x101103 0x44 (by decide) 2 (.base 7 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x101107 [0x44, 0x8B, 0x77, 0x28] (LoadPre 0x101107 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x101107 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101107 14 (.base 7 (.d8 0x28)))
      [.gpr 7] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x101107 14 (.base 7 (.d8 0x28))).toInstrSpec (mov_r32_m32_effect_step 0x101107 0x44 (by decide) 6 (.base 7 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x10110b [0x44, 0x8B, 0x67, 0x2C] (LoadPre 0x10110b (fun s => AddrMode.addr (.base 7 (.d8 0x2c)) s (0x10110b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x10110b 12 (.base 7 (.d8 0x2c)))
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR32M32Effect_footprint 0x10110b 12 (.base 7 (.d8 0x2c))).toInstrSpec (mov_r32_m32_effect_step 0x10110b 0x44 (by decide) 4 (.base 7 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x10110f [0x8B, 0x4F, 0x30] (LoadPre 0x10110f (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10110f + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x10110f 1 (.base 7 (.d8 0x30)))
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x10110f 1 (.base 7 (.d8 0x30))).toInstrSpec (mov_r32_m32_low_effect_step 0x10110f 1 (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x101112 [0x8B, 0x57, 0x34] (LoadPre 0x101112 (fun s => AddrMode.addr (.base 7 (.d8 0x34)) s (0x101112 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101112 2 (.base 7 (.d8 0x34)))
      [.gpr 7] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x101112 2 (.base 7 (.d8 0x34))).toInstrSpec (mov_r32_m32_low_effect_step 0x101112 2 (.base 7 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x101115 [0x44, 0x8B, 0x47, 0x38] (LoadPre 0x101115 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x101115 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101115 8 (.base 7 (.d8 0x38)))
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x101115 8 (.base 7 (.d8 0x38))).toInstrSpec (mov_r32_m32_effect_step 0x101115 0x44 (by decide) 0 (.base 7 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x101119 [0x44, 0x8B, 0x5F, 0x3C] (LoadPre 0x101119 (fun s => AddrMode.addr (.base 7 (.d8 0x3c)) s (0x101119 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101119 11 (.base 7 (.d8 0x3c)))
      [.gpr 7] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x101119 11 (.base 7 (.d8 0x3c))).toInstrSpec (mov_r32_m32_effect_step 0x101119 0x44 (by decide) 3 (.base 7 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (7, 7), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010d9) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(4, 4), (7, 7), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010de) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(3, 56), (4, 4), (7, 7), (11, 53), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010e0) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(3, 56), (4, 4), (7, 7), (11, 53), (13, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010e4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 56), (4, 4), (6, 60), (7, 7), (11, 53), (13, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010e7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 56), (4, 4), (6, 60), (7, 7), (11, 53), (13, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010ea) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 56), (4, 4), (6, 60), (7, 7), (11, 53), (13, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010ee) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 62), (3, 56), (4, 4), (6, 60), (7, 7), (9, 65), (11, 53), (13, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010f2) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f8 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 62), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (9, 65), (11, 53), (13, 58), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010f5) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f9 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 62), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (9, 65), (11, 53), (13, 58), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010f9) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (9, 65), (11, 53), (13, 58), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1010fc) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (9, 65), (11, 53), (13, 58), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101100) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (9, 65), (11, 53), (13, 58), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101103) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 74), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (9, 65), (10, 76), (11, 53), (13, 58), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101107) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f14 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 74), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (9, 65), (10, 76), (11, 53), (13, 58), (14, 78), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10110b) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f15 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 74), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (9, 65), (10, 76), (11, 53), (12, 80), (13, 58), (14, 78), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10110f) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f16 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 74), (1, 82), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (9, 65), (10, 76), (11, 53), (12, 80), (13, 58), (14, 78), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101112) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 74), (1, 82), (2, 84), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (9, 65), (10, 76), (11, 53), (12, 80), (13, 58), (14, 78), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101115) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 74), (1, 82), (2, 84), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (8, 86), (9, 65), (10, 76), (11, 53), (12, 80), (13, 58), (14, 78), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101119) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f19 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 74), (1, 82), (2, 84), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (8, 86), (9, 65), (10, 76), (11, 88), (12, 80), (13, 58), (14, 78), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10111d) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 90) (by decide) rfl

theorem block_l1010d5 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1010d5 :=
  Rest.liftedBlock (rest_l1010d5 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1010d5 x hx)

theorem rest_l10111d [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10111d bytes_l10111d) (entryMap (live .l10111d))
      20 0x10111d bytes_l10111d b_l10111d := by
  have f0 : InstrSpec 0x10111d [0xBF, 0x0A, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10111d) (movR32Imm32Effect 0x10111d 5 7 0xa)
      [] [] [.reg 7, .rip] :=
    (movR32Imm32Effect_footprint 0x10111d 5 7 0xa).toInstrSpec (mov_r32_imm32_effect_step 0x10111d 0xbf (by decide) 0xa) pre_rip
  have f1 : InstrSpec 0x101122 [0x48, 0x89, 0x7C, 0x24, 0x58] (StorePre 0x101122 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101122 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101122 7 (.sib 4 none 0 (.d8 0x58)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x101122 7 (.sib 4 none 0 (.d8 0x58))).toInstrSpec (mov_m64_r64_effect_step 0x101122 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x101127 [0x89, 0x5C, 0x24, 0x38] (StorePre 0x101127 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x101127 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101127 3 (.sib 4 none 0 (.d8 0x38)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101127 3 (.sib 4 none 0 (.d8 0x38))).toInstrSpec (mov_m32_r32_low_effect_step 0x101127 3 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x10112b [0x89, 0x5C, 0x24, 0x08] (StorePre 0x10112b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10112b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10112b 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10112b 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x10112b 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x10112f [0x44, 0x89, 0x4C, 0x24, 0x50] (StorePre 0x10112f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10112f + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10112f 9 (.sib 4 none 0 (.d8 0x50)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10112f 9 (.sib 4 none 0 (.d8 0x50))).toInstrSpec (mov_m32_r32_effect_step 0x10112f 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x101134 [0x89, 0x4C, 0x24, 0x34] (StorePre 0x101134 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x101134 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101134 1 (.sib 4 none 0 (.d8 0x34)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101134 1 (.sib 4 none 0 (.d8 0x34))).toInstrSpec (mov_m32_r32_low_effect_step 0x101134 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x101138 [0x89, 0x44, 0x24, 0x18] (StorePre 0x101138 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101138 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101138 0 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101138 0 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_low_effect_step 0x101138 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10113c [0x89, 0x44, 0x24, 0x04] (StorePre 0x10113c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10113c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10113c 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10113c 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x10113c 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x101140 [0x44, 0x89, 0x6C, 0x24, 0x60] (StorePre 0x101140 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x101140 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x101140 13 (.sib 4 none 0 (.d8 0x60)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x101140 13 (.sib 4 none 0 (.d8 0x60))).toInstrSpec (mov_m32_r32_effect_step 0x101140 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x101145 [0x89, 0x6C, 0x24, 0x70] (StorePre 0x101145 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101145 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101145 5 (.sib 4 none 0 (.d8 0x70)))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101145 5 (.sib 4 none 0 (.d8 0x70))).toInstrSpec (mov_m32_r32_low_effect_step 0x101145 5 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x101149 [0x89, 0x54, 0x24, 0x28] (StorePre 0x101149 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101149 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101149 2 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101149 2 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m32_r32_low_effect_step 0x101149 2 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x10114d [0x44, 0x89, 0x54, 0x24, 0x1C] (StorePre 0x10114d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10114d + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10114d 10 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10114d 10 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m32_r32_effect_step 0x10114d 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x101152 [0x89, 0x74, 0x24, 0x68] (StorePre 0x101152 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101152 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101152 6 (.sib 4 none 0 (.d8 0x68)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101152 6 (.sib 4 none 0 (.d8 0x68))).toInstrSpec (mov_m32_r32_low_effect_step 0x101152 6 (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x101156 [0x89, 0xF0] (fun s => s.RIP = 0x101156) (movR32R32Effect 0x101156 2 0 6)
      [.gpr 6] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x101156 2 0 6).toInstrSpec (mov_r32_r32_effect_step 0x101156 0xf0 (by decide)) pre_rip
  have f14 : InstrSpec 0x101158 [0x44, 0x89, 0x7C, 0x24, 0x3C] (StorePre 0x101158 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x101158 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x101158 15 (.sib 4 none 0 (.d8 0x3c)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x101158 15 (.sib 4 none 0 (.d8 0x3c))).toInstrSpec (mov_m32_r32_effect_step 0x101158 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10115d [0x44, 0x89, 0x44, 0x24, 0x2C] (StorePre 0x10115d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x10115d + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10115d 8 (.sib 4 none 0 (.d8 0x2c)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10115d 8 (.sib 4 none 0 (.d8 0x2c))).toInstrSpec (mov_m32_r32_effect_step 0x10115d 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x101162 [0x44, 0x89, 0x74, 0x24, 0x20] (StorePre 0x101162 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101162 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x101162 14 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x101162 14 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_effect_step 0x101162 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x101167 [0x8B, 0x7C, 0x24, 0x0C] (LoadPre 0x101167 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x101167 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x101167 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x101167 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x101167 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f18 : InstrSpec 0x10116b [0x8B, 0x74, 0x24, 0x10] (LoadPre 0x10116b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10116b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10116b 6 (.sib 4 none 0 (.d8 0x10)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movR32M32LowEffect_footprint 0x10116b 6 (.sib 4 none 0 (.d8 0x10))).toInstrSpec (mov_r32_m32_low_effect_step 0x10116b 6 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x10116f [0x44, 0x89, 0x5C, 0x24, 0x30] (StorePre 0x10116f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10116f + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10116f 11 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10116f 11 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m32_r32_effect_step 0x10116f 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101122) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101127) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10112b) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10112f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101134) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101138) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10113c) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101140) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101145) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101149) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10114d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101152) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101156) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101158) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10115d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101162) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101167) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10116b) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f18 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 74), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10116f) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 74), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101174) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l10111d [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10111d :=
  Rest.liftedBlock (rest_l10111d code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10111d x hx)

theorem rest_l101174 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101174 bytes_l101174) (entryMap (live .l101174))
      2 0x101174 bytes_l101174 b_l101174 := by
  have f0 : InstrSpec 0x101174 [0x44, 0x89, 0x64, 0x24, 0x24] (StorePre 0x101174 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x101174 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x101174 12 (.sib 4 none 0 (.d8 0x24)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x101174 12 (.sib 4 none 0 (.d8 0x24))).toInstrSpec (mov_m32_r32_effect_step 0x101174 0x44 (by decide) 4 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101179 [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x101179) (fun _ => nopEffect 0x101179 7)
      [] [] [.rip] :=
    (nopEffect_footprint 0x101179 7).toInstrSpec (nop_m_effect_step 0x101179 [] (by decide) (by decide) (.base 0 (.d32 0x0)) (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101179) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101180) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 55) (by decide) rfl

theorem block_l101174 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101174 :=
  Rest.liftedBlock (rest_l101174 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101174 x hx)

theorem rest_l101180 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101180 bytes_l101180) (entryMap (live .l101180))
      18 0x101180 bytes_l101180 b_l101180 := by
  have f0 : InstrSpec 0x101180 [0x44, 0x89, 0x74, 0x24, 0x78] (StorePre 0x101180 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101180 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x101180 14 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x101180 14 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_m32_r32_effect_step 0x101180 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f1 : InstrSpec 0x101185 [0x44, 0x8B, 0x74, 0x24, 0x08] (LoadPre 0x101185 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101185 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x101185 14 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x101185 14 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x101185 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10118a [0x45, 0x01, 0xCE] (fun s => s.RIP = 0x10118a) (addR32R32Effect 0x10118a 3 14 9)
      [.gpr 14, .gpr 9] [] [.reg 14, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10118a 3 14 9).toInstrSpec (add_r32_r32_rex_effect_step 0x10118a 0x45 0xce (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10118d [0x44, 0x31, 0xF1] (fun s => s.RIP = 0x10118d) (xorR32R32Effect 0x10118d 3 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10118d 3 1 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x10118d 0x44 0xf1 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101190 [0xC1, 0xC1, 0x10] (fun s => s.RIP = 0x101190) (rolR32Effect 0x101190 3 1 16)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR32Effect_footprint 0x101190 3 1 16).toInstrSpec (rol_r32_imm8_effect_step 0x101190 0xc1 0x10 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101193 [0x8B, 0x5C, 0x24, 0x04] (LoadPre 0x101193 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x101193 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x101193 3 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x101193 3 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x101193 3 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x101197 [0x01, 0xCB] (fun s => s.RIP = 0x101197) (addR32R32Effect 0x101197 2 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101197 2 3 1).toInstrSpec (add_r32_r32_effect_step 0x101197 0xcb (by decide)) pre_rip
  have f7 : InstrSpec 0x101199 [0x41, 0x31, 0xD9] (fun s => s.RIP = 0x101199) (xorR32R32Effect 0x101199 3 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101199 3 9 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x101199 0x41 0xd9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x10119c [0x41, 0xC1, 0xC1, 0x0C] (fun s => s.RIP = 0x10119c) (rolR32Effect 0x10119c 4 9 12)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR32Effect_footprint 0x10119c 4 9 12).toInstrSpec (rol_r32_imm8_rex_effect_step 0x10119c 0x41 0xc1 0xc (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1011a0 [0x45, 0x01, 0xCE] (fun s => s.RIP = 0x1011a0) (addR32R32Effect 0x1011a0 3 14 9)
      [.gpr 14, .gpr 9] [] [.reg 14, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1011a0 3 14 9).toInstrSpec (add_r32_r32_rex_effect_step 0x1011a0 0x45 0xce (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1011a3 [0x44, 0x31, 0xF1] (fun s => s.RIP = 0x1011a3) (xorR32R32Effect 0x1011a3 3 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1011a3 3 1 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x1011a3 0x44 0xf1 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1011a6 [0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x1011a6) (rolR32Effect 0x1011a6 3 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR32Effect_footprint 0x1011a6 3 1 8).toInstrSpec (rol_r32_imm8_effect_step 0x1011a6 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1011a9 [0x01, 0xCB] (fun s => s.RIP = 0x1011a9) (addR32R32Effect 0x1011a9 2 3 1)
      [.gpr 3, .gpr 1] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1011a9 2 3 1).toInstrSpec (add_r32_r32_effect_step 0x1011a9 0xcb (by decide)) pre_rip
  have f13 : InstrSpec 0x1011ab [0x89, 0x5C, 0x24, 0x04] (StorePre 0x1011ab 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1011ab + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1011ab 3 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x1011ab 3 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_low_effect_step 0x1011ab 3 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1011af [0x41, 0x31, 0xD9] (fun s => s.RIP = 0x1011af) (xorR32R32Effect 0x1011af 3 9 3)
      [.gpr 9, .gpr 3] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1011af 3 9 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x1011af 0x41 0xd9 (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x1011b2 [0x44, 0x89, 0xF3] (fun s => s.RIP = 0x1011b2) (movR32R32Effect 0x1011b2 3 3 14)
      [.gpr 14] [] [.reg 3, .rip] :=
    (movR32R32Effect_footprint 0x1011b2 3 3 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x1011b2 0x44 0xf3 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x1011b5 [0x44, 0x8B, 0x74, 0x24, 0x78] (LoadPre 0x1011b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1011b5 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1011b5 14 (.sib 4 none 0 (.d8 0x78)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR32M32Effect_footprint 0x1011b5 14 (.sib 4 none 0 (.d8 0x78))).toInstrSpec (mov_r32_m32_effect_step 0x1011b5 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x1011ba [0x41, 0xC1, 0xC1, 0x07] (fun s => s.RIP = 0x1011ba) (rolR32Effect 0x1011ba 4 9 7)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (rolR32Effect_footprint 0x1011ba 4 9 7).toInstrSpec (rol_r32_imm8_rex_effect_step 0x1011ba 0x41 0xc1 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.exec (n := 53) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101185) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 54) (RestInside.out (n := 54) f1 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 55) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 54), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10118a) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10118d) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 0), (1, 58), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101190) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 0), (1, 60), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101193) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 0), (1, 60), (2, 2), (3, 62), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101197) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 0), (1, 60), (2, 2), (3, 64), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101199) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f7 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 60), (2, 2), (3, 64), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 66), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10119c) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 60), (2, 2), (3, 64), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 68), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011a0) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 60), (2, 2), (3, 64), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 68), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011a3) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 72), (2, 2), (3, 64), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 68), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011a6) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 74), (2, 2), (3, 64), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 68), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011a9) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 74), (2, 2), (3, 76), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 68), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011ab) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 0), (1, 74), (2, 2), (3, 76), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 68), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011af) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f14 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 0), (1, 74), (2, 2), (3, 76), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 79), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011b2) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f15 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 74), (2, 2), (3, 81), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 79), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011b5) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 74), (2, 2), (3, 81), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 79), (10, 10), (11, 11), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011ba) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 74), (2, 2), (3, 81), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 85), (10, 10), (11, 11), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011be) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 87) (by decide) rfl

theorem block_l101180 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101180 :=
  Rest.liftedBlock (rest_l101180 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101180 x hx)

theorem rest_l1011be [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1011be bytes_l1011be) (entryMap (live .l1011be))
      13 0x1011be bytes_l1011be b_l1011be := by
  have f0 : InstrSpec 0x1011be [0x41, 0x01, 0xED] (fun s => s.RIP = 0x1011be) (addR32R32Effect 0x1011be 3 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1011be 3 13 5).toInstrSpec (add_r32_r32_rex_effect_step 0x1011be 0x41 0xed (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1011c1 [0x44, 0x31, 0xEA] (fun s => s.RIP = 0x1011c1) (xorR32R32Effect 0x1011c1 3 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1011c1 3 2 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1011c1 0x44 0xea (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1011c4 [0xC1, 0xC2, 0x10] (fun s => s.RIP = 0x1011c4) (rolR32Effect 0x1011c4 3 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR32Effect_footprint 0x1011c4 3 2 16).toInstrSpec (rol_r32_imm8_effect_step 0x1011c4 0xc2 0x10 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1011c7 [0x41, 0x01, 0xD2] (fun s => s.RIP = 0x1011c7) (addR32R32Effect 0x1011c7 3 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1011c7 3 10 2).toInstrSpec (add_r32_r32_rex_effect_step 0x1011c7 0x41 0xd2 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1011ca [0x44, 0x31, 0xD5] (fun s => s.RIP = 0x1011ca) (xorR32R32Effect 0x1011ca 3 5 10)
      [.gpr 5, .gpr 10] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1011ca 3 5 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1011ca 0x44 0xd5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1011cd [0xC1, 0xC5, 0x0C] (fun s => s.RIP = 0x1011cd) (rolR32Effect 0x1011cd 3 5 12)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR32Effect_footprint 0x1011cd 3 5 12).toInstrSpec (rol_r32_imm8_effect_step 0x1011cd 0xc5 0xc (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1011d0 [0x41, 0x01, 0xED] (fun s => s.RIP = 0x1011d0) (addR32R32Effect 0x1011d0 3 13 5)
      [.gpr 13, .gpr 5] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1011d0 3 13 5).toInstrSpec (add_r32_r32_rex_effect_step 0x1011d0 0x41 0xed (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1011d3 [0x44, 0x31, 0xEA] (fun s => s.RIP = 0x1011d3) (xorR32R32Effect 0x1011d3 3 2 13)
      [.gpr 2, .gpr 13] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1011d3 3 2 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1011d3 0x44 0xea (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1011d6 [0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x1011d6) (rolR32Effect 0x1011d6 3 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR32Effect_footprint 0x1011d6 3 2 8).toInstrSpec (rol_r32_imm8_effect_step 0x1011d6 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x1011d9 [0x41, 0x01, 0xD2] (fun s => s.RIP = 0x1011d9) (addR32R32Effect 0x1011d9 3 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1011d9 3 10 2).toInstrSpec (add_r32_r32_rex_effect_step 0x1011d9 0x41 0xd2 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x1011dc [0x44, 0x89, 0x54, 0x24, 0x14] (StorePre 0x1011dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1011dc + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1011dc 10 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1011dc 10 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_effect_step 0x1011dc 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x1011e1 [0x44, 0x31, 0xD5] (fun s => s.RIP = 0x1011e1) (xorR32R32Effect 0x1011e1 3 5 10)
      [.gpr 5, .gpr 10] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1011e1 3 5 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1011e1 0x44 0xd5 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x1011e4 [0xC1, 0xC5, 0x07] (fun s => s.RIP = 0x1011e4) (rolR32Effect 0x1011e4 3 5 7)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR32Effect_footprint 0x1011e4 3 5 7).toInstrSpec (rol_r32_imm8_effect_step 0x1011e4 0xc5 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011c1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011c4) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011c7) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011ca) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011cd) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011d0) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011d3) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 67), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011d6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 69), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011d9) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 69), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011dc) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 69), (3, 3), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011e1) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 69), (3, 3), (4, 4), (5, 74), (6, 6), (7, 7), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011e4) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 69), (3, 3), (4, 4), (5, 76), (6, 6), (7, 7), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011e7) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 78) (by decide) rfl

theorem block_l1011be [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1011be :=
  Rest.liftedBlock (rest_l1011be code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1011be x hx)

theorem rest_l1011e7 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1011e7 bytes_l1011e7) (entryMap (live .l1011e7))
      12 0x1011e7 bytes_l1011e7 b_l1011e7 := by
  have f0 : InstrSpec 0x1011e7 [0x44, 0x01, 0xF8] (fun s => s.RIP = 0x1011e7) (addR32R32Effect 0x1011e7 3 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1011e7 3 0 15).toInstrSpec (add_r32_r32_rex_effect_step 0x1011e7 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1011ea [0x41, 0x31, 0xC0] (fun s => s.RIP = 0x1011ea) (xorR32R32Effect 0x1011ea 3 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1011ea 3 8 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x1011ea 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1011ed [0x41, 0xC1, 0xC0, 0x10] (fun s => s.RIP = 0x1011ed) (rolR32Effect 0x1011ed 4 8 16)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR32Effect_footprint 0x1011ed 4 8 16).toInstrSpec (rol_r32_imm8_rex_effect_step 0x1011ed 0x41 0xc0 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x1011f1 [0x45, 0x01, 0xC6] (fun s => s.RIP = 0x1011f1) (addR32R32Effect 0x1011f1 3 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1011f1 3 14 8).toInstrSpec (add_r32_r32_rex_effect_step 0x1011f1 0x45 0xc6 (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1011f4 [0x45, 0x31, 0xF7] (fun s => s.RIP = 0x1011f4) (xorR32R32Effect 0x1011f4 3 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1011f4 3 15 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x1011f4 0x45 0xf7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1011f7 [0x41, 0xC1, 0xC7, 0x0C] (fun s => s.RIP = 0x1011f7) (rolR32Effect 0x1011f7 4 15 12)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR32Effect_footprint 0x1011f7 4 15 12).toInstrSpec (rol_r32_imm8_rex_effect_step 0x1011f7 0x41 0xc7 0xc (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x1011fb [0x44, 0x01, 0xF8] (fun s => s.RIP = 0x1011fb) (addR32R32Effect 0x1011fb 3 0 15)
      [.gpr 0, .gpr 15] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x1011fb 3 0 15).toInstrSpec (add_r32_r32_rex_effect_step 0x1011fb 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1011fe [0x41, 0x31, 0xC0] (fun s => s.RIP = 0x1011fe) (xorR32R32Effect 0x1011fe 3 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1011fe 3 8 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x1011fe 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101201 [0x41, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x101201) (rolR32Effect 0x101201 4 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR32Effect_footprint 0x101201 4 8 8).toInstrSpec (rol_r32_imm8_rex_effect_step 0x101201 0x41 0xc0 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101205 [0x45, 0x01, 0xC6] (fun s => s.RIP = 0x101205) (addR32R32Effect 0x101205 3 14 8)
      [.gpr 14, .gpr 8] [] [.reg 14, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101205 3 14 8).toInstrSpec (add_r32_r32_rex_effect_step 0x101205 0x45 0xc6 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101208 [0x45, 0x31, 0xF7] (fun s => s.RIP = 0x101208) (xorR32R32Effect 0x101208 3 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101208 3 15 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x101208 0x45 0xf7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10120b [0x41, 0xC1, 0xC7, 0x07] (fun s => s.RIP = 0x10120b) (rolR32Effect 0x10120b 4 15 7)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR32Effect_footprint 0x10120b 4 15 7).toInstrSpec (rol_r32_imm8_rex_effect_step 0x10120b 0x41 0xc7 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011ea) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011ed) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011f1) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011f4) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 59), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011f7) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 59), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011fb) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 59), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1011fe) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 67), (9, 9), (11, 11), (12, 12), (13, 13), (14, 59), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101201) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 59), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101205) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101208) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10120b) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10120f) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l1011e7 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1011e7 :=
  Rest.liftedBlock (rest_l1011e7 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1011e7 x hx)

theorem rest_l10120f [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10120f bytes_l10120f) (entryMap (live .l10120f))
      12 0x10120f bytes_l10120f b_l10120f := by
  have f0 : InstrSpec 0x10120f [0x01, 0xF7] (fun s => s.RIP = 0x10120f) (addR32R32Effect 0x10120f 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10120f 2 7 6).toInstrSpec (add_r32_r32_effect_step 0x10120f 0xf7 (by decide)) pre_rip
  have f1 : InstrSpec 0x101211 [0x41, 0x31, 0xFB] (fun s => s.RIP = 0x101211) (xorR32R32Effect 0x101211 3 11 7)
      [.gpr 11, .gpr 7] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101211 3 11 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x101211 0x41 0xfb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101214 [0x41, 0xC1, 0xC3, 0x10] (fun s => s.RIP = 0x101214) (rolR32Effect 0x101214 4 11 16)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR32Effect_footprint 0x101214 4 11 16).toInstrSpec (rol_r32_imm8_rex_effect_step 0x101214 0x41 0xc3 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101218 [0x45, 0x01, 0xDC] (fun s => s.RIP = 0x101218) (addR32R32Effect 0x101218 3 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101218 3 12 11).toInstrSpec (add_r32_r32_rex_effect_step 0x101218 0x45 0xdc (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10121b [0x44, 0x31, 0xE6] (fun s => s.RIP = 0x10121b) (xorR32R32Effect 0x10121b 3 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10121b 3 6 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x10121b 0x44 0xe6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10121e [0xC1, 0xC6, 0x0C] (fun s => s.RIP = 0x10121e) (rolR32Effect 0x10121e 3 6 12)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR32Effect_footprint 0x10121e 3 6 12).toInstrSpec (rol_r32_imm8_effect_step 0x10121e 0xc6 0xc (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101221 [0x01, 0xF7] (fun s => s.RIP = 0x101221) (addR32R32Effect 0x101221 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101221 2 7 6).toInstrSpec (add_r32_r32_effect_step 0x101221 0xf7 (by decide)) pre_rip
  have f7 : InstrSpec 0x101223 [0x41, 0x31, 0xFB] (fun s => s.RIP = 0x101223) (xorR32R32Effect 0x101223 3 11 7)
      [.gpr 11, .gpr 7] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101223 3 11 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x101223 0x41 0xfb (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101226 [0x41, 0xC1, 0xC3, 0x08] (fun s => s.RIP = 0x101226) (rolR32Effect 0x101226 4 11 8)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR32Effect_footprint 0x101226 4 11 8).toInstrSpec (rol_r32_imm8_rex_effect_step 0x101226 0x41 0xc3 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10122a [0x45, 0x01, 0xDC] (fun s => s.RIP = 0x10122a) (addR32R32Effect 0x10122a 3 12 11)
      [.gpr 12, .gpr 11] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10122a 3 12 11).toInstrSpec (add_r32_r32_rex_effect_step 0x10122a 0x45 0xdc (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10122d [0x44, 0x31, 0xE6] (fun s => s.RIP = 0x10122d) (xorR32R32Effect 0x10122d 3 6 12)
      [.gpr 6, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10122d 3 6 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x10122d 0x44 0xe6 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101230 [0xC1, 0xC6, 0x07] (fun s => s.RIP = 0x101230) (rolR32Effect 0x101230 3 6 7)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR32Effect_footprint 0x101230 3 6 7).toInstrSpec (rol_r32_imm8_effect_step 0x101230 0xc6 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101211) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101214) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101218) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (11, 57), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10121b) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 61), (7, 53), (8, 8), (9, 9), (11, 57), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10121e) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 63), (7, 53), (8, 8), (9, 9), (11, 57), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101221) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 8), (9, 9), (11, 57), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101223) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 8), (9, 9), (11, 67), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101226) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 8), (9, 9), (11, 69), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10122a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 63), (7, 65), (8, 8), (9, 9), (11, 69), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10122d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 73), (7, 65), (8, 8), (9, 9), (11, 69), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101230) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 75), (7, 65), (8, 8), (9, 9), (11, 69), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101233) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l10120f [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10120f :=
  Rest.liftedBlock (rest_l10120f code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10120f x hx)

theorem rest_l101233 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101233 bytes_l101233) (entryMap (live .l101233))
      13 0x101233 bytes_l101233 b_l101233 := by
  have f0 : InstrSpec 0x101233 [0x01, 0xEB] (fun s => s.RIP = 0x101233) (addR32R32Effect 0x101233 2 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101233 2 3 5).toInstrSpec (add_r32_r32_effect_step 0x101233 0xeb (by decide)) pre_rip
  have f1 : InstrSpec 0x101235 [0x41, 0x31, 0xDB] (fun s => s.RIP = 0x101235) (xorR32R32Effect 0x101235 3 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101235 3 11 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x101235 0x41 0xdb (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101238 [0x41, 0xC1, 0xC3, 0x10] (fun s => s.RIP = 0x101238) (rolR32Effect 0x101238 4 11 16)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR32Effect_footprint 0x101238 4 11 16).toInstrSpec (rol_r32_imm8_rex_effect_step 0x101238 0x41 0xc3 0x10 (by decide) (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x10123c [0x45, 0x01, 0xDE] (fun s => s.RIP = 0x10123c) (addR32R32Effect 0x10123c 3 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10123c 3 14 11).toInstrSpec (add_r32_r32_rex_effect_step 0x10123c 0x45 0xde (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x10123f [0x44, 0x31, 0xF5] (fun s => s.RIP = 0x10123f) (xorR32R32Effect 0x10123f 3 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10123f 3 5 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x10123f 0x44 0xf5 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101242 [0xC1, 0xC5, 0x0C] (fun s => s.RIP = 0x101242) (rolR32Effect 0x101242 3 5 12)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR32Effect_footprint 0x101242 3 5 12).toInstrSpec (rol_r32_imm8_effect_step 0x101242 0xc5 0xc (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101245 [0x01, 0xEB] (fun s => s.RIP = 0x101245) (addR32R32Effect 0x101245 2 3 5)
      [.gpr 3, .gpr 5] [] [.reg 3, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101245 2 3 5).toInstrSpec (add_r32_r32_effect_step 0x101245 0xeb (by decide)) pre_rip
  have f7 : InstrSpec 0x101247 [0x89, 0x5C, 0x24, 0x08] (StorePre 0x101247 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101247 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101247 3 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x101247 3 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m32_r32_low_effect_step 0x101247 3 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10124b [0x41, 0x31, 0xDB] (fun s => s.RIP = 0x10124b) (xorR32R32Effect 0x10124b 3 11 3)
      [.gpr 11, .gpr 3] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10124b 3 11 3).toInstrSpec (xor_r32_r32_rex_effect_step 0x10124b 0x41 0xdb (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10124e [0x41, 0xC1, 0xC3, 0x08] (fun s => s.RIP = 0x10124e) (rolR32Effect 0x10124e 4 11 8)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR32Effect_footprint 0x10124e 4 11 8).toInstrSpec (rol_r32_imm8_rex_effect_step 0x10124e 0x41 0xc3 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x101252 [0x45, 0x01, 0xDE] (fun s => s.RIP = 0x101252) (addR32R32Effect 0x101252 3 14 11)
      [.gpr 14, .gpr 11] [] [.reg 14, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101252 3 14 11).toInstrSpec (add_r32_r32_rex_effect_step 0x101252 0x45 0xde (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x101255 [0x44, 0x31, 0xF5] (fun s => s.RIP = 0x101255) (xorR32R32Effect 0x101255 3 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101255 3 5 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x101255 0x44 0xf5 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x101258 [0xC1, 0xC5, 0x07] (fun s => s.RIP = 0x101258) (rolR32Effect 0x101258 3 5 7)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR32Effect_footprint 0x101258 3 5 7).toInstrSpec (rol_r32_imm8_effect_step 0x101258 0xc5 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101235) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101238) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10123c) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 57), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10123f) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 61), (6, 6), (7, 7), (8, 8), (9, 9), (11, 57), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101242) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 53), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (11, 57), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101245) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (11, 57), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101247) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (11, 57), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10124b) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (11, 68), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10124e) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (11, 70), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101252) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 63), (6, 6), (7, 7), (8, 8), (9, 9), (11, 70), (12, 12), (13, 13), (14, 72), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101255) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 74), (6, 6), (7, 7), (8, 8), (9, 9), (11, 70), (12, 12), (13, 13), (14, 72), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101258) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 76), (6, 6), (7, 7), (8, 8), (9, 9), (11, 70), (12, 12), (13, 13), (14, 72), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10125b) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 78) (by decide) rfl

theorem block_l101233 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101233 :=
  Rest.liftedBlock (rest_l101233 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101233 x hx)

theorem rest_l10125b [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10125b bytes_l10125b) (entryMap (live .l10125b))
      12 0x10125b bytes_l10125b b_l10125b := by
  have f0 : InstrSpec 0x10125b [0x45, 0x01, 0xFD] (fun s => s.RIP = 0x10125b) (addR32R32Effect 0x10125b 3 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10125b 3 13 15).toInstrSpec (add_r32_r32_rex_effect_step 0x10125b 0x45 0xfd (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10125e [0x44, 0x31, 0xE9] (fun s => s.RIP = 0x10125e) (xorR32R32Effect 0x10125e 3 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10125e 3 1 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x10125e 0x44 0xe9 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x101261 [0xC1, 0xC1, 0x10] (fun s => s.RIP = 0x101261) (rolR32Effect 0x101261 3 1 16)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR32Effect_footprint 0x101261 3 1 16).toInstrSpec (rol_r32_imm8_effect_step 0x101261 0xc1 0x10 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101264 [0x41, 0x01, 0xCC] (fun s => s.RIP = 0x101264) (addR32R32Effect 0x101264 3 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101264 3 12 1).toInstrSpec (add_r32_r32_rex_effect_step 0x101264 0x41 0xcc (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x101267 [0x45, 0x31, 0xE7] (fun s => s.RIP = 0x101267) (xorR32R32Effect 0x101267 3 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101267 3 15 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x101267 0x45 0xe7 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10126a [0x41, 0xC1, 0xC7, 0x0C] (fun s => s.RIP = 0x10126a) (rolR32Effect 0x10126a 4 15 12)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR32Effect_footprint 0x10126a 4 15 12).toInstrSpec (rol_r32_imm8_rex_effect_step 0x10126a 0x41 0xc7 0xc (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10126e [0x45, 0x01, 0xFD] (fun s => s.RIP = 0x10126e) (addR32R32Effect 0x10126e 3 13 15)
      [.gpr 13, .gpr 15] [] [.reg 13, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10126e 3 13 15).toInstrSpec (add_r32_r32_rex_effect_step 0x10126e 0x45 0xfd (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101271 [0x44, 0x31, 0xE9] (fun s => s.RIP = 0x101271) (xorR32R32Effect 0x101271 3 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101271 3 1 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x101271 0x44 0xe9 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x101274 [0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x101274) (rolR32Effect 0x101274 3 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR32Effect_footprint 0x101274 3 1 8).toInstrSpec (rol_r32_imm8_effect_step 0x101274 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x101277 [0x41, 0x01, 0xCC] (fun s => s.RIP = 0x101277) (addR32R32Effect 0x101277 3 12 1)
      [.gpr 12, .gpr 1] [] [.reg 12, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101277 3 12 1).toInstrSpec (add_r32_r32_rex_effect_step 0x101277 0x41 0xcc (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10127a [0x45, 0x31, 0xE7] (fun s => s.RIP = 0x10127a) (xorR32R32Effect 0x10127a 3 15 12)
      [.gpr 15, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10127a 3 15 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x10127a 0x45 0xe7 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x10127d [0x41, 0xC1, 0xC7, 0x07] (fun s => s.RIP = 0x10127d) (rolR32Effect 0x10127d 4 15 7)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR32Effect_footprint 0x10127d 4 15 7).toInstrSpec (rol_r32_imm8_rex_effect_step 0x10127d 0x41 0xc7 0x7 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10125e) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101261) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101264) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 59), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101267) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 59), (13, 53), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10126a) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 59), (13, 53), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10126e) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 59), (13, 65), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101271) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 0), (1, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 59), (13, 65), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101274) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 59), (13, 65), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101277) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 71), (13, 65), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10127a) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 71), (13, 65), (14, 14), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10127d) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 71), (13, 65), (14, 14), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101281) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 77) (by decide) rfl

theorem block_l10125b [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10125b :=
  Rest.liftedBlock (rest_l10125b code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10125b x hx)

theorem rest_l101281 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x101281 bytes_l101281) (entryMap (live .l101281))
      15 0x101281 bytes_l101281 b_l101281 := by
  have f0 : InstrSpec 0x101281 [0x01, 0xF0] (fun s => s.RIP = 0x101281) (addR32R32Effect 0x101281 2 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101281 2 0 6).toInstrSpec (add_r32_r32_effect_step 0x101281 0xf0 (by decide)) pre_rip
  have f1 : InstrSpec 0x101283 [0x31, 0xC2] (fun s => s.RIP = 0x101283) (xorR32R32Effect 0x101283 2 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101283 2 2 0).toInstrSpec (xor_r32_r32_effect_step 0x101283 0xc2 (by decide)) pre_rip
  have f2 : InstrSpec 0x101285 [0xC1, 0xC2, 0x10] (fun s => s.RIP = 0x101285) (rolR32Effect 0x101285 3 2 16)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR32Effect_footprint 0x101285 3 2 16).toInstrSpec (rol_r32_imm8_effect_step 0x101285 0xc2 0x10 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x101288 [0x44, 0x8B, 0x54, 0x24, 0x04] (LoadPre 0x101288 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x101288 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x101288 10 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x101288 10 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_effect_step 0x101288 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10128d [0x41, 0x01, 0xD2] (fun s => s.RIP = 0x10128d) (addR32R32Effect 0x10128d 3 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10128d 3 10 2).toInstrSpec (add_r32_r32_rex_effect_step 0x10128d 0x41 0xd2 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x101290 [0x44, 0x31, 0xD6] (fun s => s.RIP = 0x101290) (xorR32R32Effect 0x101290 3 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101290 3 6 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x101290 0x44 0xd6 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x101293 [0xC1, 0xC6, 0x0C] (fun s => s.RIP = 0x101293) (rolR32Effect 0x101293 3 6 12)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR32Effect_footprint 0x101293 3 6 12).toInstrSpec (rol_r32_imm8_effect_step 0x101293 0xc6 0xc (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x101296 [0x01, 0xF0] (fun s => s.RIP = 0x101296) (addR32R32Effect 0x101296 2 0 6)
      [.gpr 0, .gpr 6] [] [.reg 0, .flags, .rip] :=
    (addR32R32Effect_footprint 0x101296 2 0 6).toInstrSpec (add_r32_r32_effect_step 0x101296 0xf0 (by decide)) pre_rip
  have f8 : InstrSpec 0x101298 [0x31, 0xC2] (fun s => s.RIP = 0x101298) (xorR32R32Effect 0x101298 2 2 0)
      [.gpr 2, .gpr 0] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x101298 2 2 0).toInstrSpec (xor_r32_r32_effect_step 0x101298 0xc2 (by decide)) pre_rip
  have f9 : InstrSpec 0x10129a [0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x10129a) (rolR32Effect 0x10129a 3 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR32Effect_footprint 0x10129a 3 2 8).toInstrSpec (rol_r32_imm8_effect_step 0x10129a 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10129d [0x41, 0x01, 0xD2] (fun s => s.RIP = 0x10129d) (addR32R32Effect 0x10129d 3 10 2)
      [.gpr 10, .gpr 2] [] [.reg 10, .flags, .rip] :=
    (addR32R32Effect_footprint 0x10129d 3 10 2).toInstrSpec (add_r32_r32_rex_effect_step 0x10129d 0x41 0xd2 (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x1012a0 [0x44, 0x89, 0x54, 0x24, 0x04] (StorePre 0x1012a0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1012a0 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1012a0 10 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1012a0 10 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m32_r32_effect_step 0x1012a0 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1012a5 [0x44, 0x31, 0xD6] (fun s => s.RIP = 0x1012a5) (xorR32R32Effect 0x1012a5 3 6 10)
      [.gpr 6, .gpr 10] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1012a5 3 6 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x1012a5 0x44 0xd6 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x1012a8 [0x44, 0x8B, 0x54, 0x24, 0x14] (LoadPre 0x1012a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1012a8 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1012a8 10 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movR32M32Effect_footprint 0x1012a8 10 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_effect_step 0x1012a8 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1012ad [0xC1, 0xC6, 0x07] (fun s => s.RIP = 0x1012ad) (rolR32Effect 0x1012ad 3 6 7)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR32Effect_footprint 0x1012ad 3 6 7).toInstrSpec (rol_r32_imm8_effect_step 0x1012ad 0xc6 0x7 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101283) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101285) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 53), (1, 1), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101288) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 53), (1, 1), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10128d) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101290) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 53), (1, 1), (2, 57), (4, 4), (5, 5), (6, 63), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101293) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 53), (1, 1), (2, 57), (4, 4), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101296) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 1), (2, 57), (4, 4), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x101298) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 67), (1, 1), (2, 69), (4, 4), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10129a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 67), (1, 1), (2, 71), (4, 4), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10129d) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 67), (1, 1), (2, 71), (4, 4), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (10, 73), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012a0) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 67), (1, 1), (2, 71), (4, 4), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (10, 73), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012a5) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 67), (1, 1), (2, 71), (4, 4), (5, 5), (6, 76), (7, 7), (8, 8), (9, 9), (10, 73), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012a8) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 67), (1, 1), (2, 71), (4, 4), (5, 5), (6, 76), (7, 7), (8, 8), (9, 9), (10, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012ad) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 67), (1, 1), (2, 71), (4, 4), (5, 5), (6, 80), (7, 7), (8, 8), (9, 9), (10, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1012b0) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.br (n := 82) (by decide) rfl

theorem block_l101281 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l101281 :=
  Rest.liftedBlock (rest_l101281 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l101281 x hx)

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

theorem_by block_l101036_eval :
    program.runBlock (dialect code) ⟨.l101036, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1010b3_eval :
    program.runBlock (dialect code) ⟨.l1010b3, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1010cc_eval :
    program.runBlock (dialect code) ⟨.l1010cc, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1010d5_eval :
    program.runBlock (dialect code) ⟨.l1010d5, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10111d_eval :
    program.runBlock (dialect code) ⟨.l10111d, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101174_eval :
    program.runBlock (dialect code) ⟨.l101174, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101180_eval :
    program.runBlock (dialect code) ⟨.l101180, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1011be_eval :
    program.runBlock (dialect code) ⟨.l1011be, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1011e7_eval :
    program.runBlock (dialect code) ⟨.l1011e7, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10120f_eval :
    program.runBlock (dialect code) ⟨.l10120f, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101233_eval :
    program.runBlock (dialect code) ⟨.l101233, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10125b_eval :
    program.runBlock (dialect code) ⟨.l10125b, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l101281_eval :
    program.runBlock (dialect code) ⟨.l101281, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
