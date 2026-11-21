import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Program
import X86Proofs.Instructions.Branch.Triple
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

theorem rest_l105100 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105100 bytes_l105100) (entryMap (live .l105100))
      14 0x105100 bytes_l105100 b_l105100 := by
  have f0 : InstrSpec 0x105100 [0x55] (PushPre 0x105100 1) (pushR64Effect 0x105100 1 5)
      [.gpr 4, .gpr 5] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105100 1 5).toInstrSpec (push_r64_effect_step 0x105100 0x55 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f1 : InstrSpec 0x105101 [0x41, 0x57] (PushPre 0x105101 2) (pushR64Effect 0x105101 2 15)
      [.gpr 4, .gpr 15] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105101 2 15).toInstrSpec (push_r64_rex_effect_step 0x105101 0x41 0x57 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f2 : InstrSpec 0x105103 [0x41, 0x56] (PushPre 0x105103 2) (pushR64Effect 0x105103 2 14)
      [.gpr 4, .gpr 14] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105103 2 14).toInstrSpec (push_r64_rex_effect_step 0x105103 0x41 0x56 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x105105 [0x41, 0x55] (PushPre 0x105105 2) (pushR64Effect 0x105105 2 13)
      [.gpr 4, .gpr 13] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105105 2 13).toInstrSpec (push_r64_rex_effect_step 0x105105 0x41 0x55 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x105107 [0x41, 0x54] (PushPre 0x105107 2) (pushR64Effect 0x105107 2 12)
      [.gpr 4, .gpr 12] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105107 2 12).toInstrSpec (push_r64_rex_effect_step 0x105107 0x41 0x54 (by decide) (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x105109 [0x53] (PushPre 0x105109 1) (pushR64Effect 0x105109 1 3)
      [.gpr 4, .gpr 3] [] [.reg 4, .rip] :=
    (pushR64Effect_footprint 0x105109 1 3).toInstrSpec (push_r64_effect_step 0x105109 0x53 (by decide)) (StorePre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x10510a [0x48, 0x83, 0xEC, 0x38] (fun s => s.RIP = 0x10510a) (subR64Imm8Effect 0x10510a 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (subR64Imm8Effect_footprint 0x10510a 4 0x38).toInstrSpec (sub_r64_imm8_effect_step 0x10510a 0x48 0xec 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x10510e [0x48, 0x89, 0xF3] (fun s => s.RIP = 0x10510e) (movR64R64Effect 0x10510e 3 6)
      [.gpr 6] [] [.reg 3, .rip] :=
    (movR64R64Effect_footprint 0x10510e 3 6).toInstrSpec (mov_r64_r64_effect_step 0x10510e 0x48 0xf3 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x105111 [0x48, 0x89, 0x7C, 0x24, 0x30] (StorePre 0x105111 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105111 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105111 7 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105111 7 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_m64_r64_effect_step 0x105111 0x48 (by decide) 7 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x105116 [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00] (StorePre 0x105116 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105116 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x105116 (.sib 4 none 0 (.d8 0x8)) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x105116 (.sib 4 none 0 (.d8 0x8)) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x105116 0x48 (by decide) (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10511f [0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00] (StorePre 0x10511f 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10511f + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10511f (.sib 4 none 0 .none) 0x0)
      [.gpr 4] [] [.rip] :=
    (movM64Imm32Effect_footprint 0x10511f (.sib 4 none 0 .none) 0x0).toInstrSpec (mov_m64_imm32_effect_step 0x10511f 0x48 (by decide) (.sib 4 none 0 .none) (by decide) (by decide) (by decide) 0x0) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x105127 [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x105127) (movR64R64Effect 0x105127 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105127 7 4).toInstrSpec (mov_r64_r64_effect_step 0x105127 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x10512a [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10512a) (movR32Imm32Effect 0x10512a 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10512a 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x10512a 0xbe (by decide) 0x8) pre_rip
  have f13 : InstrSpec 0x10512f [0xE8, 0xBC, 0x4E, 0x00, 0x00] (PushPre 0x10512f 5) (callEffect (fun _ => 0x109ff0) 0x105134)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10512f 0x109ff0 0x105134).toInstrSpec (call_rel32_effect_step 0x10512f 0x4ebc (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105101) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 2), (3, 3), (4, 55), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105103) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105105) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105107) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105109) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10510a) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10510e) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105111) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105116) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10511f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105127) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f11 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10512a) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(2, 2), (3, 67), (4, 65), (5, 5), (6, 74), (7, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10512f) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f13 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(2, 2), (3, 67), (4, 76), (5, 5), (6, 74), (7, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109ff0) f13 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 78) (by decide) (by decide) rfl rfl

theorem block_l105100 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105100 :=
  Rest.liftedBlock (rest_l105100 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105100 x hx)

theorem rest_l105134 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105134 bytes_l105134) (entryMap (live .l105134))
      18 0x105134 bytes_l105134 b_l105134 := by
  have f0 : InstrSpec 0x105134 [0x0F, 0xB7, 0x03] (LoadPre 0x105134 (fun s => AddrMode.addr (.base 3 .none) s (0x105134 + BitVec.ofNat 64 3)) 2) (movzxR32M16Effect 0x105134 3 0 (.base 3 .none))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105134 3 0 (.base 3 .none)).toInstrSpec (movzx_r32_m16_effect_step 0x105134 0 (.base 3 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105137 [0x66, 0x31, 0x04, 0x24] (StorePre 0x105137 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105137 + BitVec.ofNat 64 4)) 2) (xorMREffect 0x105137 4 16 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105137 4 0 (.sib 4 none 0 .none)).toInstrSpec (xor_m16_r16_effect_step 0x105137 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10513b [0x0F, 0xB7, 0x43, 0x02] (LoadPre 0x10513b (fun s => AddrMode.addr (.base 3 (.d8 0x2)) s (0x10513b + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10513b 4 0 (.base 3 (.d8 0x2)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10513b 4 0 (.base 3 (.d8 0x2))).toInstrSpec (movzx_r32_m16_effect_step 0x10513b 0 (.base 3 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x10513f [0x66, 0x31, 0x44, 0x24, 0x02] (StorePre 0x10513f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x10513f + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10513f 5 16 0 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x10513f 5 0 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (xor_m16_r16_effect_step 0x10513f 0 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105144 [0x0F, 0xB7, 0x43, 0x04] (LoadPre 0x105144 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x105144 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x105144 4 0 (.base 3 (.d8 0x4)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105144 4 0 (.base 3 (.d8 0x4))).toInstrSpec (movzx_r32_m16_effect_step 0x105144 0 (.base 3 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x105148 [0x66, 0x31, 0x44, 0x24, 0x04] (StorePre 0x105148 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x105148 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105148 5 16 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105148 5 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (xor_m16_r16_effect_step 0x105148 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x10514d [0x0F, 0xB7, 0x43, 0x06] (LoadPre 0x10514d (fun s => AddrMode.addr (.base 3 (.d8 0x6)) s (0x10514d + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10514d 4 0 (.base 3 (.d8 0x6)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10514d 4 0 (.base 3 (.d8 0x6))).toInstrSpec (movzx_r32_m16_effect_step 0x10514d 0 (.base 3 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x105151 [0x66, 0x31, 0x44, 0x24, 0x06] (StorePre 0x105151 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x105151 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105151 5 16 0 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105151 5 0 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (xor_m16_r16_effect_step 0x105151 0 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105156 [0x0F, 0xB7, 0x43, 0x08] (LoadPre 0x105156 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x105156 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x105156 4 0 (.base 3 (.d8 0x8)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105156 4 0 (.base 3 (.d8 0x8))).toInstrSpec (movzx_r32_m16_effect_step 0x105156 0 (.base 3 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x10515a [0x66, 0x31, 0x44, 0x24, 0x08] (StorePre 0x10515a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10515a + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10515a 5 16 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x10515a 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m16_r16_effect_step 0x10515a 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x10515f [0x0F, 0xB7, 0x43, 0x0A] (LoadPre 0x10515f (fun s => AddrMode.addr (.base 3 (.d8 0xa)) s (0x10515f + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10515f 4 0 (.base 3 (.d8 0xa)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10515f 4 0 (.base 3 (.d8 0xa))).toInstrSpec (movzx_r32_m16_effect_step 0x10515f 0 (.base 3 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x105163 [0x66, 0x31, 0x44, 0x24, 0x0A] (StorePre 0x105163 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x105163 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105163 5 16 0 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105163 5 0 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (xor_m16_r16_effect_step 0x105163 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x105168 [0x48, 0x89, 0x5C, 0x24, 0x28] (StorePre 0x105168 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105168 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105168 3 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105168 3 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_m64_r64_effect_step 0x105168 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x10516d [0x0F, 0xB7, 0x43, 0x0C] (LoadPre 0x10516d (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x10516d + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10516d 4 0 (.base 3 (.d8 0xc)))
      [.gpr 3] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10516d 4 0 (.base 3 (.d8 0xc))).toInstrSpec (movzx_r32_m16_effect_step 0x10516d 0 (.base 3 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x105171 [0x66, 0x31, 0x44, 0x24, 0x0C] (StorePre 0x105171 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105171 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105171 5 16 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105171 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (xor_m16_r16_effect_step 0x105171 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x105176 [0x45, 0x31, 0xE4] (fun s => s.RIP = 0x105176) (xorR32R32Effect 0x105176 3 12 12)
      [.gpr 12, .gpr 12] [] [.reg 12, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105176 3 12 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x105176 0x45 0xe4 (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x105179 [0x0F, 0xB7, 0x44, 0x24, 0x0E] (LoadPre 0x105179 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105179 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105179 5 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105179 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m16_effect_step 0x105179 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x10517e [0x66, 0x90] (fun s => s.RIP = 0x10517e) (fun _ => nopEffect 0x10517e 2)
      [] [] [.rip] :=
    (nopEffect_footprint 0x10517e 2).toInstrSpec (nop_66_effect_step 0x10517e) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105137) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10513b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10513f) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105144) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105148) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10514d) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105151) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105156) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10515a) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10515f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105163) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105168) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.exec (n := 71) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10516d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105171) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.exec (n := 74) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105176) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f15 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 72), (3, 3), (4, 4), (5, 5), (12, 75), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105179) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 77), (3, 3), (4, 4), (5, 5), (12, 75), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10517e) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.exec (n := 79) (ρ' := [(0, 77), (3, 3), (4, 4), (5, 5), (12, 75), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105180) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact Rest.br (n := 80) (by decide) rfl

theorem block_l105134 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105134 :=
  Rest.liftedBlock (rest_l105134 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105134 x hx)

theorem rest_l105180 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105180 bytes_l105180) (entryMap (live .l105180))
      7 0x105180 bytes_l105180 b_l105180 := by
  have f0 : InstrSpec 0x105180 [0x48, 0x8B, 0x5C, 0x24, 0x28] (LoadPre 0x105180 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105180 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105180 3 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x105180 3 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x105180 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105185 [0x66, 0x42, 0x33, 0x44, 0x63, 0x0E] (LoadPre 0x105185 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0xe)) s (0x105185 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105185 6 0 (.sib 3 (some 12) 1 (.d8 0xe)))
      [.gpr 0, .gpr 3, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x105185 6 0 (.sib 3 (some 12) 1 (.d8 0xe))).toInstrSpec (xor_r16_m16_rex_effect_step 0x105185 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10518b [0x66, 0x89, 0x44, 0x24, 0x0E] (StorePre 0x10518b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x10518b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10518b 5 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10518b 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x10518b 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x105190 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105190) (movR32Imm32Effect 0x105190 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x105190 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x105190 0xbe (by decide) 0x8) pre_rip
  have f4 : InstrSpec 0x105195 [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x105195) (movR64R64Effect 0x105195 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x105195 14 4).toInstrSpec (mov_r64_r64_effect_step 0x105195 0x49 0xe6 (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x105198 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x105198) (movR64R64Effect 0x105198 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105198 7 14).toInstrSpec (mov_r64_r64_effect_step 0x105198 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10519b [0xE8, 0x70, 0xB9, 0xFF, 0xFF] (PushPre 0x10519b 5) (callEffect (fun _ => 0x100b10) 0x1051a0)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10519b 0x100b10 0x1051a0).toInstrSpec (call_rel32_effect_step 0x10519b 0xffffb970 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105185) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10518b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105190) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (6, 58), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105195) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (6, 58), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105198) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f5 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 55), (3, 53), (4, 4), (5, 5), (6, 58), (7, 62), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10519b) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 55), (3, 53), (4, 64), (5, 5), (6, 58), (7, 62), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f6 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 66) (by decide) (by decide) rfl rfl

theorem block_l105180 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105180 :=
  Rest.liftedBlock (rest_l105180 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105180 x hx)

theorem rest_l1051a0 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1051a0 bytes_l1051a0) (entryMap (live .l1051a0))
      2 0x1051a0 bytes_l1051a0 b_l1051a0 := by
  have f0 : InstrSpec 0x1051a0 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1051a0) (movR64R64Effect 0x1051a0 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1051a0 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1051a0 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1051a3 [0xE8, 0x58, 0xAE, 0xFF, 0xFF] (PushPre 0x1051a3 5) (callEffect (fun _ => 0x100000) 0x1051a8)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1051a3 0x100000 0x1051a8).toInstrSpec (call_rel32_effect_step 0x1051a3 0xffffae58 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051a3) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100000) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l1051a0 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1051a0 :=
  Rest.liftedBlock (rest_l1051a0 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1051a0 x hx)

theorem rest_l1051a8_1 [Bindings] (code : CodeMap) :
    Rest (n := 87) code lifted (codeRange 0x1051a8 bytes_l1051a8) [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      6 0x105217 bytes_l1051a8_1 b_l1051a8_1 := by
  have f20 : InstrSpec 0x105217 [0x66, 0x89, 0x4C, 0x24, 0x0C] (StorePre 0x105217 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105217 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105217 5 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105217 5 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x105217 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10521c [0x0F, 0xB7, 0x44, 0x24, 0x0E] (LoadPre 0x10521c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x10521c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10521c 5 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10521c 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m16_effect_step 0x10521c 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f22 : InstrSpec 0x105221 [0x66, 0x42, 0x33, 0x44, 0x63, 0x1E] (LoadPre 0x105221 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1e)) s (0x105221 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105221 6 0 (.sib 3 (some 12) 1 (.d8 0x1e)))
      [.gpr 0, .gpr 3, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x105221 6 0 (.sib 3 (some 12) 1 (.d8 0x1e))).toInstrSpec (xor_r16_m16_rex_effect_step 0x105221 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x1e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f23 : InstrSpec 0x105227 [0x66, 0x89, 0x44, 0x24, 0x0E] (StorePre 0x105227 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105227 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105227 5 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105227 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x105227 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10522c [0x49, 0x83, 0xFC, 0x40] (fun s => s.RIP = 0x10522c) (cmpR64Imm8Effect 0x10522c 12 0x40)
      [.gpr 12] [] [.flags, .rip] :=
    (cmpR64Imm8Effect_footprint 0x10522c 12 0x40).toInstrSpec (cmp_r64_imm8_effect_step 0x10522c 0x49 0xfc 0x40 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 87) (RestInside.exec (n := 87) (ρ' := [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10521c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f21 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 88), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105221) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f22 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105227) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10522c) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f24 (.flag .ZF) (fun _ => rfl) (fun _ _ _ => rfl) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105230) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jcc (n := 95) (jcc_rel32_effect_step 0x105230 4 0x400) (List.cons_ne_nil _ _) (by decide) rfl (by decide) (by decide) rfl rfl

theorem rest_l1051a8 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1051a8 bytes_l1051a8) (entryMap (live .l1051a8))
      26 0x1051a8 bytes_l1051a8 b_l1051a8 := by
  have f0 : InstrSpec 0x1051a8 [0x44, 0x0F, 0xB7, 0x14, 0x24] (LoadPre 0x1051a8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1051a8 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1051a8 5 10 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x1051a8 5 10 (.sib 4 none 0 .none)).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1051a8 0x44 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1051ad [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x02] (LoadPre 0x1051ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1051ad + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1051ad 6 9 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x1051ad 6 9 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1051ad 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1051b3 [0x66, 0x46, 0x33, 0x54, 0x63, 0x10] (LoadPre 0x1051b3 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x10)) s (0x1051b3 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1051b3 6 10 (.sib 3 (some 12) 1 (.d8 0x10)))
      [.gpr 10, .gpr 3, .gpr 12] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1051b3 6 10 (.sib 3 (some 12) 1 (.d8 0x10))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1051b3 0x46 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x10)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1051b9 [0x66, 0x44, 0x89, 0x14, 0x24] (StorePre 0x1051b9 5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1051b9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1051b9 5 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1051b9 5 10 (.sib 4 none 0 .none)).toInstrSpec (mov_m16_r16_rex_effect_step 0x1051b9 0x44 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x1051be [0x66, 0x46, 0x33, 0x4C, 0x63, 0x12] (LoadPre 0x1051be (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x12)) s (0x1051be + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1051be 6 9 (.sib 3 (some 12) 1 (.d8 0x12)))
      [.gpr 9, .gpr 3, .gpr 12] [] [.reg 9, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1051be 6 9 (.sib 3 (some 12) 1 (.d8 0x12))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1051be 0x46 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x12)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x1051c4 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x02] (StorePre 0x1051c4 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1051c4 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1051c4 6 9 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1051c4 6 9 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1051c4 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x1051ca [0x44, 0x0F, 0xB7, 0x44, 0x24, 0x04] (LoadPre 0x1051ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1051ca + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1051ca 6 8 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movzxR32M16Effect_footprint 0x1051ca 6 8 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1051ca 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x1051d0 [0x66, 0x46, 0x33, 0x44, 0x63, 0x14] (LoadPre 0x1051d0 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x14)) s (0x1051d0 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1051d0 6 8 (.sib 3 (some 12) 1 (.d8 0x14)))
      [.gpr 8, .gpr 3, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1051d0 6 8 (.sib 3 (some 12) 1 (.d8 0x14))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1051d0 0x46 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x1051d6 [0x66, 0x44, 0x89, 0x44, 0x24, 0x04] (StorePre 0x1051d6 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1051d6 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1051d6 6 8 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1051d6 6 8 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1051d6 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x1051dc [0x0F, 0xB7, 0x7C, 0x24, 0x06] (LoadPre 0x1051dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1051dc + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1051dc 5 7 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x1051dc 5 7 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (movzx_r32_m16_effect_step 0x1051dc 7 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x1051e1 [0x66, 0x42, 0x33, 0x7C, 0x63, 0x16] (LoadPre 0x1051e1 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x16)) s (0x1051e1 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1051e1 6 7 (.sib 3 (some 12) 1 (.d8 0x16)))
      [.gpr 7, .gpr 3, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1051e1 6 7 (.sib 3 (some 12) 1 (.d8 0x16))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1051e1 0x42 (by decide) 7 (.sib 3 (some 12) 1 (.d8 0x16)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1051e7 [0x66, 0x89, 0x7C, 0x24, 0x06] (StorePre 0x1051e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1051e7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1051e7 5 7 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1051e7 5 7 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (mov_m16_r16_effect_step 0x1051e7 7 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1051ec [0x0F, 0xB7, 0x74, 0x24, 0x08] (LoadPre 0x1051ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1051ec + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1051ec 5 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 6, .rip] :=
    (movzxR32M16Effect_footprint 0x1051ec 5 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (movzx_r32_m16_effect_step 0x1051ec 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1051f1 [0x66, 0x42, 0x33, 0x74, 0x63, 0x18] (LoadPre 0x1051f1 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x18)) s (0x1051f1 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1051f1 6 6 (.sib 3 (some 12) 1 (.d8 0x18)))
      [.gpr 6, .gpr 3, .gpr 12] [] [.reg 6, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1051f1 6 6 (.sib 3 (some 12) 1 (.d8 0x18))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1051f1 0x42 (by decide) 6 (.sib 3 (some 12) 1 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x1051f7 [0x66, 0x89, 0x74, 0x24, 0x08] (StorePre 0x1051f7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1051f7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1051f7 5 6 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1051f7 5 6 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m16_r16_effect_step 0x1051f7 6 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x1051fc [0x0F, 0xB7, 0x54, 0x24, 0x0A] (LoadPre 0x1051fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x1051fc + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1051fc 5 2 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x1051fc 5 2 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m16_effect_step 0x1051fc 2 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x105201 [0x66, 0x42, 0x33, 0x54, 0x63, 0x1A] (LoadPre 0x105201 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1a)) s (0x105201 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105201 6 2 (.sib 3 (some 12) 1 (.d8 0x1a)))
      [.gpr 2, .gpr 3, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x105201 6 2 (.sib 3 (some 12) 1 (.d8 0x1a))).toInstrSpec (xor_r16_m16_rex_effect_step 0x105201 0x42 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x1a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f17 : InstrSpec 0x105207 [0x66, 0x89, 0x54, 0x24, 0x0A] (StorePre 0x105207 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x105207 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105207 5 2 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105207 5 2 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m16_r16_effect_step 0x105207 2 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f18 : InstrSpec 0x10520c [0x0F, 0xB7, 0x4C, 0x24, 0x0C] (LoadPre 0x10520c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10520c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10520c 5 1 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movzxR32M16Effect_footprint 0x10520c 5 1 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (movzx_r32_m16_effect_step 0x10520c 1 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x105211 [0x66, 0x42, 0x33, 0x4C, 0x63, 0x1C] (LoadPre 0x105211 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1c)) s (0x105211 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105211 6 1 (.sib 3 (some 12) 1 (.d8 0x1c)))
      [.gpr 1, .gpr 3, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x105211 6 1 (.sib 3 (some 12) 1 (.d8 0x1c))).toInstrSpec (xor_r16_m16_rex_effect_step 0x105211 0x42 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051ad) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051b3) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051b9) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.exec (n := 59) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 55), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051be) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f4 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 61) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051c4) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 62) (RestInside.exec (n := 62) (ρ' := [(3, 3), (4, 4), (5, 5), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051ca) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f6 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 63), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051d0) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f7 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051d6) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(3, 3), (4, 4), (5, 5), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051dc) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f9 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 68), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051e1) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f10 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051e7) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051ec) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f12 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 73), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051f1) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f13 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051f7) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.exec (n := 77) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1051fc) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f15 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(2, 78), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105201) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f16 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105207) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10520c) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f18 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(1, 83), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105211) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f19 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105217) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1051a8_1 code

theorem block_l1051a8 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1051a8 :=
  Rest.liftedBlock (rest_l1051a8 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1051a8 x hx)

theorem rest_l105236 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105236 bytes_l105236) (entryMap (live .l105236))
      3 0x105236 bytes_l105236 b_l105236 := by
  have f0 : InstrSpec 0x105236 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105236) (movR32Imm32Effect 0x105236 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x105236 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x105236 0xbe (by decide) 0x8) pre_rip
  have f1 : InstrSpec 0x10523b [0x48, 0x89, 0xE7] (fun s => s.RIP = 0x10523b) (movR64R64Effect 0x10523b 7 4)
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10523b 7 4).toInstrSpec (mov_r64_r64_effect_step 0x10523b 0x48 0xe7 (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10523e [0xE8, 0xCD, 0xB8, 0xFF, 0xFF] (PushPre 0x10523e 5) (callEffect (fun _ => 0x100b10) 0x105243)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10523e 0x100b10 0x105243).toInstrSpec (call_rel32_effect_step 0x10523e 0xffffb8cd (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10523b) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 4), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10523e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f2 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 59) (by decide) (by decide) rfl rfl

theorem block_l105236 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105236 :=
  Rest.liftedBlock (rest_l105236 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105236 x hx)

theorem rest_l105243_6 [Bindings] (code : CodeMap) :
    Rest (n := 283) code lifted (codeRange 0x105243 bytes_l105243) [(0, 181), (1, 280), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]
      18 0x105426 bytes_l105243_6 b_l105243_6 := by
  have f120 : InstrSpec 0x105426 [0x8B, 0x54, 0x24, 0x1C] (LoadPre 0x105426 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x105426 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105426 2 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x105426 2 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_r32_m32_low_effect_step 0x105426 2 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f121 : InstrSpec 0x10542a [0x44, 0x31, 0xDA] (fun s => s.RIP = 0x10542a) (xorR32R32Effect 0x10542a 3 2 11)
      [.gpr 2, .gpr 11] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10542a 3 2 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10542a 0x44 0xda (by decide) (by decide)) pre_rip
  have f122 : InstrSpec 0x10542d [0x44, 0x31, 0xDE] (fun s => s.RIP = 0x10542d) (xorR32R32Effect 0x10542d 3 6 11)
      [.gpr 6, .gpr 11] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10542d 3 6 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x10542d 0x44 0xde (by decide) (by decide)) pre_rip
  have f123 : InstrSpec 0x105430 [0x89, 0xD1] (fun s => s.RIP = 0x105430) (movR32R32Effect 0x105430 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105430 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x105430 0xd1 (by decide)) pre_rip
  have f124 : InstrSpec 0x105432 [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x105432) (rolR16Effect 0x105432 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x105432 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x105432 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f125 : InstrSpec 0x105436 [0x66, 0x42, 0x33, 0x4C, 0x63, 0x2C] (LoadPre 0x105436 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2c)) s (0x105436 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105436 6 1 (.sib 3 (some 12) 1 (.d8 0x2c)))
      [.gpr 1, .gpr 3, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x105436 6 1 (.sib 3 (some 12) 1 (.d8 0x2c))).toInstrSpec (xor_r16_m16_rex_effect_step 0x105436 0x42 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x2c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f126 : InstrSpec 0x10543c [0x31, 0xCE] (fun s => s.RIP = 0x10543c) (xorR32R32Effect 0x10543c 2 6 1)
      [.gpr 6, .gpr 1] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10543c 2 6 1).toInstrSpec (xor_r32_r32_effect_step 0x10543c 0xce (by decide)) pre_rip
  have f127 : InstrSpec 0x10543e [0x66, 0x89, 0x74, 0x24, 0x0C] (StorePre 0x10543e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10543e + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10543e 5 6 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x10543e 5 6 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x10543e 6 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f128 : InstrSpec 0x105443 [0x89, 0xD1] (fun s => s.RIP = 0x105443) (movR32R32Effect 0x105443 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105443 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x105443 0xd1 (by decide)) pre_rip
  have f129 : InstrSpec 0x105445 [0x31, 0xC1] (fun s => s.RIP = 0x105445) (xorR32R32Effect 0x105445 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105445 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105445 0xc1 (by decide)) pre_rip
  have f130 : InstrSpec 0x105447 [0x66, 0x41, 0xC1, 0xC6, 0x08] (fun s => s.RIP = 0x105447) (rolR16Effect 0x105447 5 14 8)
      [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 14, .flags, .rip] :=
    (rolR16Effect_footprint 0x105447 5 14 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x105447 0x41 0xc6 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f131 : InstrSpec 0x10544c [0x66, 0x46, 0x33, 0x74, 0x63, 0x2E] (LoadPre 0x10544c (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2e)) s (0x10544c + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x10544c 6 14 (.sib 3 (some 12) 1 (.d8 0x2e)))
      [.gpr 14, .gpr 3, .gpr 12] [] [.reg 14, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x10544c 6 14 (.sib 3 (some 12) 1 (.d8 0x2e))).toInstrSpec (xor_r16_m16_rex_effect_step 0x10544c 0x46 (by decide) 6 (.sib 3 (some 12) 1 (.d8 0x2e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f132 : InstrSpec 0x105452 [0x44, 0x31, 0xF1] (fun s => s.RIP = 0x105452) (xorR32R32Effect 0x105452 3 1 14)
      [.gpr 1, .gpr 14] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105452 3 1 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x105452 0x44 0xf1 (by decide) (by decide)) pre_rip
  have f133 : InstrSpec 0x105455 [0x66, 0x89, 0x4C, 0x24, 0x0E] (StorePre 0x105455 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105455 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105455 5 1 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105455 5 1 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x105455 1 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f134 : InstrSpec 0x10545a [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x10545a) (movR32Imm32Effect 0x10545a 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x10545a 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x10545a 0xbe (by decide) 0x8) pre_rip
  have f135 : InstrSpec 0x10545f [0x49, 0x89, 0xE6] (fun s => s.RIP = 0x10545f) (movR64R64Effect 0x10545f 14 4)
      [.gpr 4] [] [.reg 14, .rip] :=
    (movR64R64Effect_footprint 0x10545f 14 4).toInstrSpec (mov_r64_r64_effect_step 0x10545f 0x49 0xe6 (by decide) (by decide)) pre_rip
  have f136 : InstrSpec 0x105462 [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x105462) (movR64R64Effect 0x105462 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x105462 7 14).toInstrSpec (mov_r64_r64_effect_step 0x105462 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f137 : InstrSpec 0x105465 [0xE8, 0xA6, 0xB6, 0xFF, 0xFF] (PushPre 0x105465 5) (callEffect (fun _ => 0x100b10) 0x10546a)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105465 0x100b10 0x10546a).toInstrSpec (call_rel32_effect_step 0x105465 0xffffb6a6 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 283) (RestInside.out (n := 283) f120 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 284) (ρ' := [(0, 181), (1, 280), (2, 283), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10542a) f120 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 285) (RestInside.out (n := 285) f121 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 286) (ρ' := [(0, 181), (1, 280), (2, 285), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10542d) f121 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 287) (RestInside.out (n := 287) f122 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 288) (ρ' := [(0, 181), (1, 280), (2, 285), (3, 191), (4, 4), (5, 197), (6, 287), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105430) f122 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 289) (RestInside.out (n := 289) f123 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 290) (ρ' := [(0, 181), (1, 289), (2, 285), (3, 191), (4, 4), (5, 197), (6, 287), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105432) f123 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 291) (RestInside.out (n := 291) f124 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 292) (ρ' := [(0, 181), (1, 291), (2, 285), (3, 191), (4, 4), (5, 197), (6, 287), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105436) f124 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 293) (RestInside.out (n := 293) f125 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 294) (ρ' := [(0, 181), (1, 293), (2, 285), (3, 191), (4, 4), (5, 197), (6, 287), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10543c) f125 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 295) (RestInside.out (n := 295) f126 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 296) (ρ' := [(0, 181), (1, 293), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10543e) f126 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 297) (RestInside.exec (n := 297) (ρ' := [(0, 181), (1, 293), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105443) f127 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 298) (RestInside.out (n := 298) f128 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 299) (ρ' := [(0, 181), (1, 298), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105445) f128 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 300) (RestInside.out (n := 300) f129 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 301) (ρ' := [(0, 181), (1, 300), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105447) f129 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 302) (RestInside.out (n := 302) f130 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 303) (ρ' := [(0, 181), (1, 300), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 302), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10544c) f130 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 304) (RestInside.out (n := 304) f131 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 305) (ρ' := [(0, 181), (1, 300), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 304), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105452) f131 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 306) (RestInside.out (n := 306) f132 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 307) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 304), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105455) f132 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 308) (RestInside.exec (n := 308) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 4), (5, 197), (6, 295), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 304), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10545a) f133 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 309) (RestInside.out (n := 309) f134 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 310) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 4), (5, 197), (6, 309), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 304), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10545f) f134 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 311) (RestInside.out (n := 311) f135 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 312) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 4), (5, 197), (6, 309), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 311), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105462) f135 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 313) (RestInside.out (n := 313) f136 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 314) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 4), (5, 197), (6, 309), (7, 313), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 311), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105465) f136 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 315) (RestInside.out (n := 315) f137 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 316) (ρ' := [(0, 181), (1, 306), (2, 285), (3, 191), (4, 315), (5, 197), (6, 309), (7, 313), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 311), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f137 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 317) (by decide) (by decide) rfl rfl

theorem rest_l105243_5 [Bindings] (code : CodeMap) :
    Rest (n := 246) code lifted (codeRange 0x105243 bytes_l105243) [(0, 181), (1, 244), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]
      38 0x1053de bytes_l105243_5 b_l105243_5 := by
  have f100 : InstrSpec 0x1053de [0x66, 0x89, 0x7C, 0x24, 0x06] (StorePre 0x1053de 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1053de + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1053de 5 7 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1053de 5 7 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (mov_m16_r16_effect_step 0x1053de 7 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f101 : InstrSpec 0x1053e3 [0x89, 0xCA] (fun s => s.RIP = 0x1053e3) (movR32R32Effect 0x1053e3 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1053e3 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x1053e3 0xca (by decide)) pre_rip
  have f102 : InstrSpec 0x1053e5 [0x89, 0xCF] (fun s => s.RIP = 0x1053e5) (movR32R32Effect 0x1053e5 2 7 1)
      [.gpr 1] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x1053e5 2 7 1).toInstrSpec (mov_r32_r32_effect_step 0x1053e5 0xcf (by decide)) pre_rip
  have f103 : InstrSpec 0x1053e7 [0x66, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x1053e7) (rolR16Effect 0x1053e7 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR16Effect_footprint 0x1053e7 4 2 8).toInstrSpec (rol_r16_imm8_effect_step 0x1053e7 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f104 : InstrSpec 0x1053eb [0x45, 0x31, 0xEF] (fun s => s.RIP = 0x1053eb) (xorR32R32Effect 0x1053eb 3 15 13)
      [.gpr 15, .gpr 13] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053eb 3 15 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1053eb 0x45 0xef (by decide) (by decide)) pre_rip
  have f105 : InstrSpec 0x1053ee [0x66, 0x42, 0x33, 0x54, 0x63, 0x28] (LoadPre 0x1053ee (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x28)) s (0x1053ee + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1053ee 6 2 (.sib 3 (some 12) 1 (.d8 0x28)))
      [.gpr 2, .gpr 3, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1053ee 6 2 (.sib 3 (some 12) 1 (.d8 0x28))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1053ee 0x42 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f106 : InstrSpec 0x1053f4 [0x45, 0x31, 0xF7] (fun s => s.RIP = 0x1053f4) (xorR32R32Effect 0x1053f4 3 15 14)
      [.gpr 15, .gpr 14] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053f4 3 15 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x1053f4 0x45 0xf7 (by decide) (by decide)) pre_rip
  have f107 : InstrSpec 0x1053f7 [0x41, 0x31, 0xD7] (fun s => s.RIP = 0x1053f7) (xorR32R32Effect 0x1053f7 3 15 2)
      [.gpr 15, .gpr 2] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053f7 3 15 2).toInstrSpec (xor_r32_r32_rex_effect_step 0x1053f7 0x41 0xd7 (by decide) (by decide)) pre_rip
  have f108 : InstrSpec 0x1053fa [0x8B, 0x4C, 0x24, 0x18] (LoadPre 0x1053fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1053fa + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1053fa 1 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1053fa 1 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_r32_m32_low_effect_step 0x1053fa 1 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f109 : InstrSpec 0x1053fe [0x44, 0x8B, 0x44, 0x24, 0x14] (LoadPre 0x1053fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1053fe + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1053fe 8 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x1053fe 8 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_effect_step 0x1053fe 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f110 : InstrSpec 0x105403 [0x44, 0x31, 0xC1] (fun s => s.RIP = 0x105403) (xorR32R32Effect 0x105403 3 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105403 3 1 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x105403 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f111 : InstrSpec 0x105406 [0x66, 0x44, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x105406 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105406 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x105406 6 15 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 15, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105406 6 15 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m16_r16_rex_effect_step 0x105406 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f112 : InstrSpec 0x10540c [0x89, 0xCA] (fun s => s.RIP = 0x10540c) (movR32R32Effect 0x10540c 2 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x10540c 2 2 1).toInstrSpec (mov_r32_r32_effect_step 0x10540c 0xca (by decide)) pre_rip
  have f113 : InstrSpec 0x10540e [0x89, 0xCE] (fun s => s.RIP = 0x10540e) (movR32R32Effect 0x10540e 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x10540e 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x10540e 0xce (by decide)) pre_rip
  have f114 : InstrSpec 0x105410 [0x66, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x105410) (rolR16Effect 0x105410 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR16Effect_footprint 0x105410 4 2 8).toInstrSpec (rol_r16_imm8_effect_step 0x105410 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f115 : InstrSpec 0x105414 [0x66, 0x42, 0x33, 0x54, 0x63, 0x2A] (LoadPre 0x105414 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2a)) s (0x105414 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105414 6 2 (.sib 3 (some 12) 1 (.d8 0x2a)))
      [.gpr 2, .gpr 3, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x105414 6 2 (.sib 3 (some 12) 1 (.d8 0x2a))).toInstrSpec (xor_r16_m16_rex_effect_step 0x105414 0x42 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x2a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f116 : InstrSpec 0x10541a [0x89, 0xF9] (fun s => s.RIP = 0x10541a) (movR32R32Effect 0x10541a 2 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10541a 2 1 7).toInstrSpec (mov_r32_r32_effect_step 0x10541a 0xf9 (by decide)) pre_rip
  have f117 : InstrSpec 0x10541c [0x44, 0x31, 0xC1] (fun s => s.RIP = 0x10541c) (xorR32R32Effect 0x10541c 3 1 8)
      [.gpr 1, .gpr 8] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10541c 3 1 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x10541c 0x44 0xc1 (by decide) (by decide)) pre_rip
  have f118 : InstrSpec 0x10541f [0x31, 0xD1] (fun s => s.RIP = 0x10541f) (xorR32R32Effect 0x10541f 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10541f 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x10541f 0xd1 (by decide)) pre_rip
  have f119 : InstrSpec 0x105421 [0x66, 0x89, 0x4C, 0x24, 0x0A] (StorePre 0x105421 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x105421 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105421 5 1 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105421 5 1 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m16_r16_effect_step 0x105421 1 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 246) (RestInside.exec (n := 246) (ρ' := [(0, 181), (1, 244), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053e3) f100 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 247) (RestInside.out (n := 247) f101 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 248) (ρ' := [(0, 181), (1, 244), (2, 247), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053e5) f101 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 249) (RestInside.out (n := 249) f102 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 250) (ρ' := [(0, 181), (1, 244), (2, 247), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053e7) f102 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 251) (RestInside.out (n := 251) f103 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 252) (ρ' := [(0, 181), (1, 244), (2, 251), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053eb) f103 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 253) (RestInside.out (n := 253) f104 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 254) (ρ' := [(0, 181), (1, 244), (2, 251), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 253), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053ee) f104 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 255) (RestInside.out (n := 255) f105 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 256) (ρ' := [(0, 181), (1, 244), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 253), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053f4) f105 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 257) (RestInside.out (n := 257) f106 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 258) (ρ' := [(0, 181), (1, 244), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 257), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053f7) f106 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 259) (RestInside.out (n := 259) f107 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 260) (ρ' := [(0, 181), (1, 244), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053fa) f107 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 261) (RestInside.out (n := 261) f108 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 262) (ρ' := [(0, 181), (1, 261), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053fe) f108 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 263) (RestInside.out (n := 263) f109 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 264) (ρ' := [(0, 181), (1, 261), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105403) f109 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 265) (RestInside.out (n := 265) f110 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 266) (ρ' := [(0, 181), (1, 265), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105406) f110 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 267) (RestInside.exec (n := 267) (ρ' := [(0, 181), (1, 265), (2, 255), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10540c) f111 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 268) (RestInside.out (n := 268) f112 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 269) (ρ' := [(0, 181), (1, 265), (2, 268), (3, 191), (4, 4), (5, 197), (6, 121), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10540e) f112 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 270) (RestInside.out (n := 270) f113 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 271) (ρ' := [(0, 181), (1, 265), (2, 268), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105410) f113 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 272) (RestInside.out (n := 272) f114 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 273) (ρ' := [(0, 181), (1, 265), (2, 272), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105414) f114 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 274) (RestInside.out (n := 274) f115 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 275) (ρ' := [(0, 181), (1, 265), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10541a) f115 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 276) (RestInside.out (n := 276) f116 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 277) (ρ' := [(0, 181), (1, 276), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10541c) f116 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 278) (RestInside.out (n := 278) f117 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 279) (ρ' := [(0, 181), (1, 278), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10541f) f117 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 280) (RestInside.out (n := 280) f118 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 281) (ρ' := [(0, 181), (1, 280), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105421) f118 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 282) (RestInside.exec (n := 282) (ρ' := [(0, 181), (1, 280), (2, 274), (3, 191), (4, 4), (5, 197), (6, 270), (7, 249), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105426) f119 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l105243_6 code

theorem rest_l105243_4 [Bindings] (code : CodeMap) :
    Rest (n := 208) code lifted (codeRange 0x105243 bytes_l105243) [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 206), (9, 202), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      58 0x105394 bytes_l105243_4 b_l105243_4 := by
  have f80 : InstrSpec 0x105394 [0x66, 0x46, 0x33, 0x44, 0x63, 0x22] (LoadPre 0x105394 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x22)) s (0x105394 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105394 6 8 (.sib 3 (some 12) 1 (.d8 0x22)))
      [.gpr 8, .gpr 3, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x105394 6 8 (.sib 3 (some 12) 1 (.d8 0x22))).toInstrSpec (xor_r16_m16_rex_effect_step 0x105394 0x46 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x22)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f81 : InstrSpec 0x10539a [0x45, 0x31, 0xF1] (fun s => s.RIP = 0x10539a) (xorR32R32Effect 0x10539a 3 9 14)
      [.gpr 9, .gpr 14] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10539a 3 9 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x10539a 0x45 0xf1 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x10539d [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x10539d) (xorR32R32Effect 0x10539d 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10539d 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x10539d 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f83 : InstrSpec 0x1053a0 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x02] (StorePre 0x1053a0 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1053a0 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1053a0 6 9 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1053a0 6 9 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1053a0 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f84 : InstrSpec 0x1053a6 [0x31, 0xCF] (fun s => s.RIP = 0x1053a6) (xorR32R32Effect 0x1053a6 2 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053a6 2 7 1).toInstrSpec (xor_r32_r32_effect_step 0x1053a6 0xcf (by decide)) pre_rip
  have f85 : InstrSpec 0x1053a8 [0x31, 0xCA] (fun s => s.RIP = 0x1053a8) (xorR32R32Effect 0x1053a8 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053a8 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1053a8 0xca (by decide)) pre_rip
  have f86 : InstrSpec 0x1053aa [0x41, 0x89, 0xF8] (fun s => s.RIP = 0x1053aa) (movR32R32Effect 0x1053aa 3 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x1053aa 3 8 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x1053aa 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f87 : InstrSpec 0x1053ad [0x66, 0x41, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x1053ad) (rolR16Effect 0x1053ad 5 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR16Effect_footprint 0x1053ad 5 8 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x1053ad 0x41 0xc0 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f88 : InstrSpec 0x1053b2 [0x66, 0x46, 0x33, 0x44, 0x63, 0x24] (LoadPre 0x1053b2 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x24)) s (0x1053b2 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1053b2 6 8 (.sib 3 (some 12) 1 (.d8 0x24)))
      [.gpr 8, .gpr 3, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1053b2 6 8 (.sib 3 (some 12) 1 (.d8 0x24))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1053b2 0x46 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x24)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f89 : InstrSpec 0x1053b8 [0x44, 0x31, 0xC2] (fun s => s.RIP = 0x1053b8) (xorR32R32Effect 0x1053b8 3 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053b8 3 2 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1053b8 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f90 : InstrSpec 0x1053bb [0x41, 0x31, 0xF7] (fun s => s.RIP = 0x1053bb) (xorR32R32Effect 0x1053bb 3 15 6)
      [.gpr 15, .gpr 6] [] [.reg 15, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053bb 3 15 6).toInstrSpec (xor_r32_r32_rex_effect_step 0x1053bb 0x41 0xf7 (by decide) (by decide)) pre_rip
  have f91 : InstrSpec 0x1053be [0x66, 0x89, 0x54, 0x24, 0x04] (StorePre 0x1053be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1053be + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1053be 5 2 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1053be 5 2 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m16_r16_effect_step 0x1053be 2 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f92 : InstrSpec 0x1053c3 [0x44, 0x89, 0xFA] (fun s => s.RIP = 0x1053c3) (movR32R32Effect 0x1053c3 3 2 15)
      [.gpr 15] [] [.reg 2, .rip] :=
    (movR32R32Effect_footprint 0x1053c3 3 2 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1053c3 0x44 0xfa (by decide) (by decide)) pre_rip
  have f93 : InstrSpec 0x1053c6 [0x66, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x1053c6) (rolR16Effect 0x1053c6 4 2 8)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (rolR16Effect_footprint 0x1053c6 4 2 8).toInstrSpec (rol_r16_imm8_effect_step 0x1053c6 0xc2 0x8 (by decide) (by decide)) pre_rip
  have f94 : InstrSpec 0x1053ca [0x66, 0x42, 0x33, 0x54, 0x63, 0x26] (LoadPre 0x1053ca (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x26)) s (0x1053ca + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1053ca 6 2 (.sib 3 (some 12) 1 (.d8 0x26)))
      [.gpr 2, .gpr 3, .gpr 12] [] [.reg 2, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1053ca 6 2 (.sib 3 (some 12) 1 (.d8 0x26))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1053ca 0x42 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x26)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f95 : InstrSpec 0x1053d0 [0x31, 0xF7] (fun s => s.RIP = 0x1053d0) (xorR32R32Effect 0x1053d0 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053d0 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x1053d0 0xf7 (by decide)) pre_rip
  have f96 : InstrSpec 0x1053d2 [0x44, 0x31, 0xF7] (fun s => s.RIP = 0x1053d2) (xorR32R32Effect 0x1053d2 3 7 14)
      [.gpr 7, .gpr 14] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053d2 3 7 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x1053d2 0x44 0xf7 (by decide) (by decide)) pre_rip
  have f97 : InstrSpec 0x1053d5 [0x31, 0xD7] (fun s => s.RIP = 0x1053d5) (xorR32R32Effect 0x1053d5 2 7 2)
      [.gpr 7, .gpr 2] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053d5 2 7 2).toInstrSpec (xor_r32_r32_effect_step 0x1053d5 0xd7 (by decide)) pre_rip
  have f98 : InstrSpec 0x1053d7 [0x8B, 0x4C, 0x24, 0x20] (LoadPre 0x1053d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1053d7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1053d7 1 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR32M32LowEffect_footprint 0x1053d7 1 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r32_m32_low_effect_step 0x1053d7 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f99 : InstrSpec 0x1053db [0x44, 0x31, 0xE9] (fun s => s.RIP = 0x1053db) (xorR32R32Effect 0x1053db 3 1 13)
      [.gpr 1, .gpr 13] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1053db 3 1 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1053db 0x44 0xe9 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 208) (RestInside.out (n := 208) f80 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 209) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 208), (9, 202), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10539a) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 210) (RestInside.out (n := 210) f81 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 211) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 208), (9, 210), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10539d) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f82 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 208), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053a0) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.exec (n := 214) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 208), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053a6) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 215) (RestInside.out (n := 215) f84 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 216) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 208), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053a8) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 217) (RestInside.out (n := 217) f85 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 218) (ρ' := [(0, 181), (1, 107), (2, 217), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 208), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053aa) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 219) (RestInside.out (n := 219) f86 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 220) (ρ' := [(0, 181), (1, 107), (2, 217), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 219), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053ad) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f87 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 181), (1, 107), (2, 217), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 221), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053b2) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 223) (RestInside.out (n := 223) f88 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 224) (ρ' := [(0, 181), (1, 107), (2, 217), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053b8) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 225) (RestInside.out (n := 225) f89 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 226) (ρ' := [(0, 181), (1, 107), (2, 225), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053bb) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 227) (RestInside.out (n := 227) f90 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 228) (ρ' := [(0, 181), (1, 107), (2, 225), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053be) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 229) (RestInside.exec (n := 229) (ρ' := [(0, 181), (1, 107), (2, 225), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053c3) f91 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 230) (RestInside.out (n := 230) f92 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 231) (ρ' := [(0, 181), (1, 107), (2, 230), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053c6) f92 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 232) (RestInside.out (n := 232) f93 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 233) (ρ' := [(0, 181), (1, 107), (2, 232), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053ca) f93 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 234) (RestInside.out (n := 234) f94 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 235) (ρ' := [(0, 181), (1, 107), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 215), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053d0) f94 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 236) (RestInside.out (n := 236) f95 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 237) (ρ' := [(0, 181), (1, 107), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 236), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053d2) f95 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 238) (RestInside.out (n := 238) f96 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 239) (ρ' := [(0, 181), (1, 107), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 238), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053d5) f96 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 240) (RestInside.out (n := 240) f97 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 241) (ρ' := [(0, 181), (1, 107), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053d7) f97 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 242) (RestInside.out (n := 242) f98 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 243) (ρ' := [(0, 181), (1, 242), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053db) f98 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 244) (RestInside.out (n := 244) f99 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 245) (ρ' := [(0, 181), (1, 244), (2, 234), (3, 191), (4, 4), (5, 197), (6, 121), (7, 240), (8, 223), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 227), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1053de) f99 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l105243_5 code

theorem rest_l105243_3 [Bindings] (code : CodeMap) :
    Rest (n := 169) code lifted (codeRange 0x105243 bytes_l105243) [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 161), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      78 0x105345 bytes_l105243_3 b_l105243_3 := by
  have f60 : InstrSpec 0x105345 [0x45, 0x89, 0xF2] (fun s => s.RIP = 0x105345) (movR32R32Effect 0x105345 3 10 14)
      [.gpr 14] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x105345 3 10 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x105345 0x45 0xf2 (by decide) (by decide)) pre_rip
  have f61 : InstrSpec 0x105348 [0x66, 0x41, 0xC1, 0xC2, 0x0A] (fun s => s.RIP = 0x105348) (rolR16Effect 0x105348 5 10 10)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x105348 5 10 10).toInstrSpec (rol_r16_imm8_rex_effect_step 0x105348 0x41 0xc2 0xa (by decide) (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x10534d [0x41, 0x81, 0xE2, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x10534d) (andR32Imm32Effect 0x10534d 7 10 0x3333)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10534d 7 10 0x3333).toInstrSpec (and_r32_imm32_rex_effect_step 0x10534d 0x41 0xe2 0x3333 (by decide) (by decide) (by decide)) pre_rip
  have f63 : InstrSpec 0x105354 [0x44, 0x89, 0xF0] (fun s => s.RIP = 0x105354) (movR32R32Effect 0x105354 3 0 14)
      [.gpr 14] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105354 3 0 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x105354 0x44 0xf0 (by decide) (by decide)) pre_rip
  have f64 : InstrSpec 0x105357 [0x66, 0xC1, 0xC0, 0x0E] (fun s => s.RIP = 0x105357) (rolR16Effect 0x105357 4 0 14)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x105357 4 0 14).toInstrSpec (rol_r16_imm8_effect_step 0x105357 0xc0 0xe (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x10535b [0x25, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x10535b) (andEaxImm32Effect 0x10535b 0xffffcccc)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10535b 0xffffcccc).toInstrSpec (and_eax_imm32_effect_step 0x10535b 0xffffcccc) pre_rip
  have f66 : InstrSpec 0x105360 [0x44, 0x09, 0xD0] (fun s => s.RIP = 0x105360) (orR32R32Effect 0x105360 3 0 10)
      [.gpr 0, .gpr 10] [] [.reg 0, .flags, .rip] :=
    (orR32R32Effect_footprint 0x105360 3 0 10).toInstrSpec (or_r32_r32_rex_effect_step 0x105360 0x44 0xd0 (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x105363 [0x41, 0x31, 0xE9] (fun s => s.RIP = 0x105363) (xorR32R32Effect 0x105363 3 9 5)
      [.gpr 9, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105363 3 9 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x105363 0x41 0xe9 (by decide) (by decide)) pre_rip
  have f68 : InstrSpec 0x105366 [0x41, 0x31, 0xC6] (fun s => s.RIP = 0x105366) (xorR32R32Effect 0x105366 3 14 0)
      [.gpr 14, .gpr 0] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105366 3 14 0).toInstrSpec (xor_r32_r32_rex_effect_step 0x105366 0x41 0xc6 (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x105369 [0x45, 0x89, 0xCA] (fun s => s.RIP = 0x105369) (movR32R32Effect 0x105369 3 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x105369 3 10 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x105369 0x45 0xca (by decide) (by decide)) pre_rip
  have f70 : InstrSpec 0x10536c [0x66, 0x41, 0xC1, 0xC2, 0x08] (fun s => s.RIP = 0x10536c) (rolR16Effect 0x10536c 5 10 8)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x10536c 5 10 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x10536c 0x41 0xc2 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f71 : InstrSpec 0x105371 [0x48, 0x8B, 0x5C, 0x24, 0x28] (LoadPre 0x105371 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105371 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105371 3 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x105371 3 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x105371 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f72 : InstrSpec 0x105376 [0x66, 0x46, 0x33, 0x54, 0x63, 0x20] (LoadPre 0x105376 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x20)) s (0x105376 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105376 6 10 (.sib 3 (some 12) 1 (.d8 0x20)))
      [.gpr 10, .gpr 3, .gpr 12] [] [.reg 10, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x105376 6 10 (.sib 3 (some 12) 1 (.d8 0x20))).toInstrSpec (xor_r16_m16_rex_effect_step 0x105376 0x46 (by decide) 2 (.sib 3 (some 12) 1 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f73 : InstrSpec 0x10537c [0x44, 0x31, 0xF5] (fun s => s.RIP = 0x10537c) (xorR32R32Effect 0x10537c 3 5 14)
      [.gpr 5, .gpr 14] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10537c 3 5 14).toInstrSpec (xor_r32_r32_rex_effect_step 0x10537c 0x44 0xf5 (by decide) (by decide)) pre_rip
  have f74 : InstrSpec 0x10537f [0x44, 0x31, 0xD5] (fun s => s.RIP = 0x10537f) (xorR32R32Effect 0x10537f 3 5 10)
      [.gpr 5, .gpr 10] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10537f 3 5 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10537f 0x44 0xd5 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x105382 [0x66, 0x89, 0x2C, 0x24] (StorePre 0x105382 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105382 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x105382 4 5 (.sib 4 none 0 .none))
      [.gpr 5, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105382 4 5 (.sib 4 none 0 .none)).toInstrSpec (mov_m16_r16_effect_step 0x105382 5 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x105386 [0x44, 0x31, 0xC2] (fun s => s.RIP = 0x105386) (xorR32R32Effect 0x105386 3 2 8)
      [.gpr 2, .gpr 8] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105386 3 2 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x105386 0x44 0xc2 (by decide) (by decide)) pre_rip
  have f77 : InstrSpec 0x105389 [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x105389) (xorR32R32Effect 0x105389 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105389 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x105389 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x10538c [0x41, 0x89, 0xD0] (fun s => s.RIP = 0x10538c) (movR32R32Effect 0x10538c 3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x10538c 3 8 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x10538c 0x41 0xd0 (by decide) (by decide)) pre_rip
  have f79 : InstrSpec 0x10538f [0x66, 0x41, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x10538f) (rolR16Effect 0x10538f 5 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR16Effect_footprint 0x10538f 5 8 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x10538f 0x41 0xc0 0x8 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 169) (RestInside.out (n := 169) f60 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 170) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 169), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105348) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 171) (RestInside.out (n := 171) f61 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 172) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 171), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10534d) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f62 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105354) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f63 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 175), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105357) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f64 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 177), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10535b) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f65 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 179), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105360) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f66 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105363) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.out (n := 183) f67 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 184) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 173), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105366) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 185) (RestInside.out (n := 185) f68 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 186) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 173), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105369) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 187) (RestInside.out (n := 187) f69 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 188) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 187), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10536c) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 189) (RestInside.out (n := 189) f70 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 190) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 189), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105371) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 191) (RestInside.out (n := 191) f71 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 192) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 191), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 189), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105376) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 193) (RestInside.out (n := 193) f72 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 194) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 191), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 183), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10537c) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f73 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 191), (4, 4), (5, 195), (6, 121), (7, 55), (8, 97), (9, 183), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10537f) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f74 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 97), (9, 183), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105382) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.exec (n := 199) (ρ' := [(0, 181), (1, 107), (2, 57), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 97), (9, 183), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105386) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 200) (RestInside.out (n := 200) f76 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 201) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 97), (9, 183), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105389) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 202) (RestInside.out (n := 202) f77 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 203) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 97), (9, 202), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10538c) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 204) (RestInside.out (n := 204) f78 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 205) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 204), (9, 202), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10538f) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 206) (RestInside.out (n := 206) f79 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 207) (ρ' := [(0, 181), (1, 107), (2, 200), (3, 191), (4, 4), (5, 197), (6, 121), (7, 55), (8, 206), (9, 202), (10, 193), (11, 165), (12, 12), (13, 134), (14, 185), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105394) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l105243_4 code

theorem rest_l105243_2 [Bindings] (code : CodeMap) :
    Rest (n := 132) code lifted (codeRange 0x105243 bytes_l105243) [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 130), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      98 0x1052e8 bytes_l105243_2 b_l105243_2 := by
  have f40 : InstrSpec 0x1052e8 [0x41, 0x81, 0xE5, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x1052e8) (andR32Imm32Effect 0x1052e8 7 13 0xffffcccc)
      [.gpr 13] [] [.reg 13, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1052e8 7 13 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x1052e8 0x41 0xe5 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x1052ef [0x41, 0x09, 0xC5] (fun s => s.RIP = 0x1052ef) (orR32R32Effect 0x1052ef 3 13 0)
      [.gpr 13, .gpr 0] [] [.reg 13, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1052ef 3 13 0).toInstrSpec (or_r32_r32_rex_effect_step 0x1052ef 0x41 0xc5 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x1052f2 [0x44, 0x89, 0x54, 0x24, 0x18] (StorePre 0x1052f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1052f2 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1052f2 10 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1052f2 10 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_effect_step 0x1052f2 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f43 : InstrSpec 0x1052f7 [0x44, 0x89, 0xD0] (fun s => s.RIP = 0x1052f7) (movR32R32Effect 0x1052f7 3 0 10)
      [.gpr 10] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1052f7 3 0 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x1052f7 0x44 0xd0 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1052fa [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x1052fa) (rolR16Effect 0x1052fa 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x1052fa 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x1052fa 0xc0 0xa (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x1052fe [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x1052fe) (andEaxImm32Effect 0x1052fe 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1052fe 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x1052fe 0x3333) pre_rip
  have f46 : InstrSpec 0x105303 [0x45, 0x89, 0xD3] (fun s => s.RIP = 0x105303) (movR32R32Effect 0x105303 3 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x105303 3 11 10).toInstrSpec (mov_r32_r32_rex_effect_step 0x105303 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x105306 [0x66, 0x41, 0xC1, 0xC3, 0x0E] (fun s => s.RIP = 0x105306) (rolR16Effect 0x105306 5 11 14)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR16Effect_footprint 0x105306 5 11 14).toInstrSpec (rol_r16_imm8_rex_effect_step 0x105306 0x41 0xc3 0xe (by decide) (by decide) (by decide)) pre_rip
  have f48 : InstrSpec 0x10530b [0x41, 0x81, 0xE3, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x10530b) (andR32Imm32Effect 0x10530b 7 11 0xffffcccc)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10530b 7 11 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x10530b 0x41 0xe3 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x105312 [0x89, 0x5C, 0x24, 0x1C] (StorePre 0x105312 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x105312 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x105312 3 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 3, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105312 3 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m32_r32_low_effect_step 0x105312 3 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f50 : InstrSpec 0x105316 [0x41, 0x89, 0xDA] (fun s => s.RIP = 0x105316) (movR32R32Effect 0x105316 3 10 3)
      [.gpr 3] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x105316 3 10 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x105316 0x41 0xda (by decide) (by decide)) pre_rip
  have f51 : InstrSpec 0x105319 [0x66, 0x41, 0xC1, 0xC2, 0x0A] (fun s => s.RIP = 0x105319) (rolR16Effect 0x105319 5 10 10)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x105319 5 10 10).toInstrSpec (rol_r16_imm8_rex_effect_step 0x105319 0x41 0xc2 0xa (by decide) (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x10531e [0x41, 0x09, 0xC3] (fun s => s.RIP = 0x10531e) (orR32R32Effect 0x10531e 3 11 0)
      [.gpr 11, .gpr 0] [] [.reg 11, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10531e 3 11 0).toInstrSpec (or_r32_r32_rex_effect_step 0x10531e 0x41 0xc3 (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x105321 [0x44, 0x89, 0x5C, 0x24, 0x14] (StorePre 0x105321 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x105321 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x105321 11 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x105321 11 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_effect_step 0x105321 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f54 : InstrSpec 0x105326 [0x41, 0x89, 0xDB] (fun s => s.RIP = 0x105326) (movR32R32Effect 0x105326 3 11 3)
      [.gpr 3] [] [.reg 11, .rip] :=
    (movR32R32Effect_footprint 0x105326 3 11 3).toInstrSpec (mov_r32_r32_rex_effect_step 0x105326 0x41 0xdb (by decide) (by decide)) pre_rip
  have f55 : InstrSpec 0x105329 [0x66, 0x41, 0xC1, 0xC3, 0x0E] (fun s => s.RIP = 0x105329) (rolR16Effect 0x105329 5 11 14)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (rolR16Effect_footprint 0x105329 5 11 14).toInstrSpec (rol_r16_imm8_rex_effect_step 0x105329 0x41 0xc3 0xe (by decide) (by decide) (by decide)) pre_rip
  have f56 : InstrSpec 0x10532e [0x41, 0x81, 0xE2, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x10532e) (andR32Imm32Effect 0x10532e 7 10 0x3333)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x10532e 7 10 0x3333).toInstrSpec (and_r32_imm32_rex_effect_step 0x10532e 0x41 0xe2 0x3333 (by decide) (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x105335 [0x41, 0x81, 0xE3, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x105335) (andR32Imm32Effect 0x105335 7 11 0xffffcccc)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105335 7 11 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x105335 0x41 0xe3 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x10533c [0x45, 0x09, 0xD3] (fun s => s.RIP = 0x10533c) (orR32R32Effect 0x10533c 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10533c 3 11 10).toInstrSpec (or_r32_r32_rex_effect_step 0x10533c 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f59 : InstrSpec 0x10533f [0x44, 0x0F, 0xB7, 0x74, 0x24, 0x0E] (LoadPre 0x10533f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x10533f + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10533f 6 14 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M16Effect_footprint 0x10533f 6 14 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10533f 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f40 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 132), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052ef) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f41 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052f2) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.exec (n := 136) (ρ' := [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052f7) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f43 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 137), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052fa) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f44 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 139), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052fe) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f45 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105303) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f46 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (11, 143), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105306) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f47 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (11, 145), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10530b) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f48 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (11, 147), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105312) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.exec (n := 149) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (11, 147), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105316) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 150) (RestInside.out (n := 150) f50 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 151) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 150), (11, 147), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105319) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 152) (RestInside.out (n := 152) f51 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 153) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 152), (11, 147), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10531e) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 154) (RestInside.out (n := 154) f52 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 155) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 152), (11, 154), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105321) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 156) (RestInside.exec (n := 156) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 152), (11, 154), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105326) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 157) (RestInside.out (n := 157) f54 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 158) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 152), (11, 157), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105329) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f55 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 152), (11, 159), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10532e) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f56 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 161), (11, 159), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105335) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f57 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 161), (11, 163), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10533c) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f58 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 161), (11, 165), (12, 12), (13, 134), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10533f) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 167) (RestInside.out (n := 167) f59 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 168) (ρ' := [(0, 141), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 161), (11, 165), (12, 12), (13, 134), (14, 167), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105345) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l105243_3 code

theorem rest_l105243_1 [Bindings] (code : CodeMap) :
    Rest (n := 93) code lifted (codeRange 0x105243 bytes_l105243) [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (8, 91), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]
      118 0x10529a bytes_l105243_1 b_l105243_1 := by
  have f20 : InstrSpec 0x10529a [0x89, 0xFE] (fun s => s.RIP = 0x10529a) (movR32R32Effect 0x10529a 2 6 7)
      [.gpr 7] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x10529a 2 6 7).toInstrSpec (mov_r32_r32_effect_step 0x10529a 0xfe (by decide)) pre_rip
  have f21 : InstrSpec 0x10529c [0x66, 0xC1, 0xC6, 0x0A] (fun s => s.RIP = 0x10529c) (rolR16Effect 0x10529c 4 6 10)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR16Effect_footprint 0x10529c 4 6 10).toInstrSpec (rol_r16_imm8_effect_step 0x10529c 0xc6 0xa (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x1052a0 [0x41, 0x09, 0xC0] (fun s => s.RIP = 0x1052a0) (orR32R32Effect 0x1052a0 3 8 0)
      [.gpr 8, .gpr 0] [] [.reg 8, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1052a0 3 8 0).toInstrSpec (or_r32_r32_rex_effect_step 0x1052a0 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x1052a3 [0x89, 0xF9] (fun s => s.RIP = 0x1052a3) (movR32R32Effect 0x1052a3 2 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1052a3 2 1 7).toInstrSpec (mov_r32_r32_effect_step 0x1052a3 0xf9 (by decide)) pre_rip
  have f24 : InstrSpec 0x1052a5 [0x66, 0xC1, 0xC1, 0x0E] (fun s => s.RIP = 0x1052a5) (rolR16Effect 0x1052a5 4 1 14)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x1052a5 4 1 14).toInstrSpec (rol_r16_imm8_effect_step 0x1052a5 0xc1 0xe (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x1052a9 [0x81, 0xE6, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x1052a9) (andR32Imm32Effect 0x1052a9 6 6 0x3333)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1052a9 6 6 0x3333).toInstrSpec (and_r32_imm32_effect_step 0x1052a9 0xe6 0x3333 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1052af [0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x1052af) (andR32Imm32Effect 0x1052af 6 1 0xffffcccc)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1052af 6 1 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x1052af 0xe1 0xffffcccc (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x1052b5 [0x09, 0xF1] (fun s => s.RIP = 0x1052b5) (orR32R32Effect 0x1052b5 2 1 6)
      [.gpr 1, .gpr 6] [] [.reg 1, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1052b5 2 1 6).toInstrSpec (or_r32_r32_effect_step 0x1052b5 0xf1 (by decide)) pre_rip
  have f28 : InstrSpec 0x1052b7 [0x44, 0x89, 0xF8] (fun s => s.RIP = 0x1052b7) (movR32R32Effect 0x1052b7 3 0 15)
      [.gpr 15] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1052b7 3 0 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1052b7 0x44 0xf8 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1052ba [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x1052ba) (rolR16Effect 0x1052ba 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x1052ba 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x1052ba 0xc0 0xa (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1052be [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x1052be) (andEaxImm32Effect 0x1052be 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1052be 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x1052be 0x3333) pre_rip
  have f31 : InstrSpec 0x1052c3 [0x44, 0x89, 0xFE] (fun s => s.RIP = 0x1052c3) (movR32R32Effect 0x1052c3 3 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x1052c3 3 6 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x1052c3 0x44 0xfe (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x1052c6 [0x66, 0xC1, 0xC6, 0x0E] (fun s => s.RIP = 0x1052c6) (rolR16Effect 0x1052c6 4 6 14)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR16Effect_footprint 0x1052c6 4 6 14).toInstrSpec (rol_r16_imm8_effect_step 0x1052c6 0xc6 0xe (by decide) (by decide)) pre_rip
  have f33 : InstrSpec 0x1052ca [0x81, 0xE6, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x1052ca) (andR32Imm32Effect 0x1052ca 6 6 0xffffcccc)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1052ca 6 6 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x1052ca 0xe6 0xffffcccc (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1052d0 [0x09, 0xC6] (fun s => s.RIP = 0x1052d0) (orR32R32Effect 0x1052d0 2 6 0)
      [.gpr 6, .gpr 0] [] [.reg 6, .flags, .rip] :=
    (orR32R32Effect_footprint 0x1052d0 2 6 0).toInstrSpec (or_r32_r32_effect_step 0x1052d0 0xc6 (by decide)) pre_rip
  have f35 : InstrSpec 0x1052d2 [0x44, 0x89, 0x6C, 0x24, 0x20] (StorePre 0x1052d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1052d2 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1052d2 13 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 13, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x1052d2 13 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m32_r32_effect_step 0x1052d2 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f36 : InstrSpec 0x1052d7 [0x44, 0x89, 0xE8] (fun s => s.RIP = 0x1052d7) (movR32R32Effect 0x1052d7 3 0 13)
      [.gpr 13] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x1052d7 3 0 13).toInstrSpec (mov_r32_r32_rex_effect_step 0x1052d7 0x44 0xe8 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x1052da [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x1052da) (rolR16Effect 0x1052da 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x1052da 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x1052da 0xc0 0xa (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x1052de [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x1052de) (andEaxImm32Effect 0x1052de 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x1052de 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x1052de 0x3333) pre_rip
  have f39 : InstrSpec 0x1052e3 [0x66, 0x41, 0xC1, 0xC5, 0x0E] (fun s => s.RIP = 0x1052e3) (rolR16Effect 0x1052e3 5 13 14)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR16Effect_footprint 0x1052e3 5 13 14).toInstrSpec (rol_r16_imm8_rex_effect_step 0x1052e3 0x41 0xc5 0xe (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (6, 93), (7, 55), (8, 91), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10529c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f21 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (6, 95), (7, 55), (8, 91), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052a0) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.out (n := 97) f22 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 98) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (6, 95), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052a3) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 99) (RestInside.out (n := 99) f23 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 100) (ρ' := [(0, 85), (1, 99), (2, 57), (3, 65), (4, 4), (5, 79), (6, 95), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052a5) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 101) (RestInside.out (n := 101) f24 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 102) (ρ' := [(0, 85), (1, 101), (2, 57), (3, 65), (4, 4), (5, 79), (6, 95), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052a9) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 103) (RestInside.out (n := 103) f25 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 104) (ρ' := [(0, 85), (1, 101), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052af) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 105) (RestInside.out (n := 105) f26 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 106) (ρ' := [(0, 85), (1, 105), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052b5) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 107) (RestInside.out (n := 107) f27 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 108) (ρ' := [(0, 85), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052b7) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 109) (RestInside.out (n := 109) f28 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 110) (ρ' := [(0, 109), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052ba) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 111) (RestInside.out (n := 111) f29 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 112) (ρ' := [(0, 111), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052be) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f30 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 103), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052c3) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f31 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 115), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052c6) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f32 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 117), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052ca) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f33 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 119), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052d0) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f34 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052d2) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.exec (n := 123) (ρ' := [(0, 113), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052d7) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 124) (RestInside.out (n := 124) f36 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 125) (ρ' := [(0, 124), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052da) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 126) (RestInside.out (n := 126) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 127) (ρ' := [(0, 126), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052de) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f38 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052e3) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f39 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 128), (1, 107), (2, 57), (3, 65), (4, 4), (5, 79), (6, 121), (7, 55), (8, 97), (9, 53), (10, 63), (12, 12), (13, 130), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1052e8) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l105243_2 code

theorem rest_l105243 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105243 bytes_l105243) (entryMap (live .l105243))
      138 0x105243 bytes_l105243 b_l105243 := by
  have f0 : InstrSpec 0x105243 [0x44, 0x8B, 0x0C, 0x24] (LoadPre 0x105243 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105243 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x105243 9 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movR32M32Effect_footprint 0x105243 9 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_effect_step 0x105243 0x44 (by decide) 1 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105247 [0x8B, 0x7C, 0x24, 0x04] (LoadPre 0x105247 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x105247 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105247 7 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movR32M32LowEffect_footprint 0x105247 7 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x105247 7 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x10524b [0x0F, 0xB7, 0x54, 0x24, 0x02] (LoadPre 0x10524b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x10524b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10524b 5 2 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movzxR32M16Effect_footprint 0x10524b 5 2 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (movzx_r32_m16_effect_step 0x10524b 2 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105250 [0x44, 0x0F, 0xB7, 0x7C, 0x24, 0x06] (LoadPre 0x105250 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x105250 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x105250 6 15 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 4] [] [.reg 15, .rip] :=
    (movzxR32M16Effect_footprint 0x105250 6 15 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x105250 0x44 (by decide) 7 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x105256 [0x44, 0x8B, 0x6C, 0x24, 0x08] (LoadPre 0x105256 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105256 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x105256 13 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 13, .rip] :=
    (movR32M32Effect_footprint 0x105256 13 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x105256 0x44 (by decide) 5 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10525b [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x0A] (LoadPre 0x10525b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x10525b + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10525b 6 10 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 10, .rip] :=
    (movzxR32M16Effect_footprint 0x10525b 6 10 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10525b 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105261 [0x8B, 0x5C, 0x24, 0x0C] (LoadPre 0x105261 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105261 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105261 3 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR32M32LowEffect_footprint 0x105261 3 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x105261 3 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x105265 [0x44, 0x89, 0xC8] (fun s => s.RIP = 0x105265) (movR32R32Effect 0x105265 3 0 9)
      [.gpr 9] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105265 3 0 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x105265 0x44 0xc8 (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x105268 [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x105268) (rolR16Effect 0x105268 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x105268 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x105268 0xc0 0xa (by decide) (by decide)) pre_rip
  have f9 : InstrSpec 0x10526c [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x10526c) (andEaxImm32Effect 0x10526c 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x10526c 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x10526c 0x3333) pre_rip
  have f10 : InstrSpec 0x105271 [0x44, 0x89, 0xCD] (fun s => s.RIP = 0x105271) (movR32R32Effect 0x105271 3 5 9)
      [.gpr 9] [] [.reg 5, .rip] :=
    (movR32R32Effect_footprint 0x105271 3 5 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x105271 0x44 0xcd (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x105274 [0x66, 0xC1, 0xC5, 0x0E] (fun s => s.RIP = 0x105274) (rolR16Effect 0x105274 4 5 14)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR16Effect_footprint 0x105274 4 5 14).toInstrSpec (rol_r16_imm8_effect_step 0x105274 0xc5 0xe (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x105278 [0x81, 0xE5, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x105278) (andR32Imm32Effect 0x105278 6 5 0xffffcccc)
      [.gpr 5] [] [.reg 5, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105278 6 5 0xffffcccc).toInstrSpec (and_r32_imm32_effect_step 0x105278 0xe5 0xffffcccc (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10527e [0x09, 0xC5] (fun s => s.RIP = 0x10527e) (orR32R32Effect 0x10527e 2 5 0)
      [.gpr 5, .gpr 0] [] [.reg 5, .flags, .rip] :=
    (orR32R32Effect_footprint 0x10527e 2 5 0).toInstrSpec (or_r32_r32_effect_step 0x10527e 0xc5 (by decide)) pre_rip
  have f14 : InstrSpec 0x105280 [0x89, 0xD0] (fun s => s.RIP = 0x105280) (movR32R32Effect 0x105280 2 0 2)
      [.gpr 2] [] [.reg 0, .rip] :=
    (movR32R32Effect_footprint 0x105280 2 0 2).toInstrSpec (mov_r32_r32_effect_step 0x105280 0xd0 (by decide)) pre_rip
  have f15 : InstrSpec 0x105282 [0x66, 0xC1, 0xC0, 0x0A] (fun s => s.RIP = 0x105282) (rolR16Effect 0x105282 4 0 10)
      [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 0, .flags, .rip] :=
    (rolR16Effect_footprint 0x105282 4 0 10).toInstrSpec (rol_r16_imm8_effect_step 0x105282 0xc0 0xa (by decide) (by decide)) pre_rip
  have f16 : InstrSpec 0x105286 [0x25, 0x33, 0x33, 0x00, 0x00] (fun s => s.RIP = 0x105286) (andEaxImm32Effect 0x105286 0x3333)
      [.gpr 0] [] [.reg 0, .flags, .rip] :=
    (andEaxImm32Effect_footprint 0x105286 0x3333).toInstrSpec (and_eax_imm32_effect_step 0x105286 0x3333) pre_rip
  have f17 : InstrSpec 0x10528b [0x41, 0x89, 0xD0] (fun s => s.RIP = 0x10528b) (movR32R32Effect 0x10528b 3 8 2)
      [.gpr 2] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x10528b 3 8 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x10528b 0x41 0xd0 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x10528e [0x66, 0x41, 0xC1, 0xC0, 0x0E] (fun s => s.RIP = 0x10528e) (rolR16Effect 0x10528e 5 8 14)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR16Effect_footprint 0x10528e 5 8 14).toInstrSpec (rol_r16_imm8_rex_effect_step 0x10528e 0x41 0xc0 0xe (by decide) (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x105293 [0x41, 0x81, 0xE0, 0xCC, 0xCC, 0xFF, 0xFF] (fun s => s.RIP = 0x105293) (andR32Imm32Effect 0x105293 7 8 0xffffcccc)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105293 7 8 0xffffcccc).toInstrSpec (and_r32_imm32_rex_effect_step 0x105293 0x41 0xe0 0xffffcccc (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(4, 4), (9, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105247) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(4, 4), (7, 55), (9, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10524b) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 57), (4, 4), (7, 55), (9, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105250) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 57), (4, 4), (7, 55), (9, 53), (12, 12), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105256) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 57), (4, 4), (7, 55), (9, 53), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10525b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 57), (4, 4), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105261) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 57), (3, 65), (4, 4), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105265) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (2, 57), (3, 65), (4, 4), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105268) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(0, 69), (2, 57), (3, 65), (4, 4), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10526c) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (2, 57), (3, 65), (4, 4), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105271) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 71), (2, 57), (3, 65), (4, 4), (5, 73), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105274) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f11 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 76) (ρ' := [(0, 71), (2, 57), (3, 65), (4, 4), (5, 75), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105278) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f12 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 71), (2, 57), (3, 65), (4, 4), (5, 77), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10527e) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f13 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 71), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105280) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 81), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105282) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 83), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105286) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f16 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10528b) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f17 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (8, 87), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10528e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f18 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (8, 89), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105293) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f19 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 85), (2, 57), (3, 65), (4, 4), (5, 79), (7, 55), (8, 91), (9, 53), (10, 63), (12, 12), (13, 61), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10529a) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l105243_1 code

theorem block_l105243 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105243 :=
  Rest.liftedBlock (rest_l105243 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105243 x hx)

theorem rest_l10546a [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x10546a bytes_l10546a) (entryMap (live .l10546a))
      2 0x10546a bytes_l10546a b_l10546a := by
  have f0 : InstrSpec 0x10546a [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x10546a) (movR64R64Effect 0x10546a 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10546a 7 14).toInstrSpec (mov_r64_r64_effect_step 0x10546a 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x10546d [0xE8, 0x0E, 0xB1, 0xFF, 0xFF] (PushPre 0x10546d 5) (callEffect (fun _ => 0x100580) 0x105472)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x10546d 0x100580 0x105472).toInstrSpec (call_rel32_effect_step 0x10546d 0xffffb10e (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10546d) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100580) f1 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 57) (by decide) (by decide) rfl rfl

theorem block_l10546a [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l10546a :=
  Rest.liftedBlock (rest_l10546a code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l10546a x hx)

theorem rest_l105472 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105472 bytes_l105472) (entryMap (live .l105472))
      19 0x105472 bytes_l105472 b_l105472 := by
  have f0 : InstrSpec 0x105472 [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x30] (LoadPre 0x105472 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x30)) s (0x105472 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x105472 6 0 (.sib 3 (some 12) 1 (.d8 0x30)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105472 6 0 (.sib 3 (some 12) 1 (.d8 0x30))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x105472 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x105478 [0x66, 0x31, 0x04, 0x24] (StorePre 0x105478 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105478 + BitVec.ofNat 64 4)) 2) (xorMREffect 0x105478 4 16 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105478 4 0 (.sib 4 none 0 .none)).toInstrSpec (xor_m16_r16_effect_step 0x105478 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f2 : InstrSpec 0x10547c [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x32] (LoadPre 0x10547c (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x32)) s (0x10547c + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10547c 6 0 (.sib 3 (some 12) 1 (.d8 0x32)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10547c 6 0 (.sib 3 (some 12) 1 (.d8 0x32))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10547c 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x32)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x105482 [0x66, 0x31, 0x44, 0x24, 0x02] (StorePre 0x105482 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x105482 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105482 5 16 0 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105482 5 0 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (xor_m16_r16_effect_step 0x105482 0 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f4 : InstrSpec 0x105487 [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x34] (LoadPre 0x105487 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x34)) s (0x105487 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x105487 6 0 (.sib 3 (some 12) 1 (.d8 0x34)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105487 6 0 (.sib 3 (some 12) 1 (.d8 0x34))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x105487 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x34)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f5 : InstrSpec 0x10548d [0x66, 0x31, 0x44, 0x24, 0x04] (StorePre 0x10548d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10548d + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10548d 5 16 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x10548d 5 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (xor_m16_r16_effect_step 0x10548d 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f6 : InstrSpec 0x105492 [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x36] (LoadPre 0x105492 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x36)) s (0x105492 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x105492 6 0 (.sib 3 (some 12) 1 (.d8 0x36)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105492 6 0 (.sib 3 (some 12) 1 (.d8 0x36))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x105492 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x36)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f7 : InstrSpec 0x105498 [0x66, 0x31, 0x44, 0x24, 0x06] (StorePre 0x105498 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x105498 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105498 5 16 0 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105498 5 0 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (xor_m16_r16_effect_step 0x105498 0 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x10549d [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x38] (LoadPre 0x10549d (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x38)) s (0x10549d + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x10549d 6 0 (.sib 3 (some 12) 1 (.d8 0x38)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10549d 6 0 (.sib 3 (some 12) 1 (.d8 0x38))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x10549d 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x38)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1054a3 [0x66, 0x31, 0x44, 0x24, 0x08] (StorePre 0x1054a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1054a3 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1054a3 5 16 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x1054a3 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m16_r16_effect_step 0x1054a3 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f10 : InstrSpec 0x1054a8 [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x3A] (LoadPre 0x1054a8 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3a)) s (0x1054a8 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1054a8 6 0 (.sib 3 (some 12) 1 (.d8 0x3a)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1054a8 6 0 (.sib 3 (some 12) 1 (.d8 0x3a))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1054a8 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x3a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f11 : InstrSpec 0x1054ae [0x66, 0x31, 0x44, 0x24, 0x0A] (StorePre 0x1054ae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x1054ae + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1054ae 5 16 0 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x1054ae 5 0 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (xor_m16_r16_effect_step 0x1054ae 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x1054b3 [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x3C] (LoadPre 0x1054b3 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3c)) s (0x1054b3 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1054b3 6 0 (.sib 3 (some 12) 1 (.d8 0x3c)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1054b3 6 0 (.sib 3 (some 12) 1 (.d8 0x3c))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1054b3 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x3c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x1054b9 [0x66, 0x31, 0x44, 0x24, 0x0C] (StorePre 0x1054b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1054b9 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1054b9 5 16 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x1054b9 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (xor_m16_r16_effect_step 0x1054b9 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f14 : InstrSpec 0x1054be [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x3E] (LoadPre 0x1054be (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3e)) s (0x1054be + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1054be 6 0 (.sib 3 (some 12) 1 (.d8 0x3e)))
      [.gpr 3, .gpr 12] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x1054be 6 0 (.sib 3 (some 12) 1 (.d8 0x3e))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1054be 0x42 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x3e)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f15 : InstrSpec 0x1054c4 [0x66, 0x31, 0x44, 0x24, 0x0E] (StorePre 0x1054c4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1054c4 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1054c4 5 16 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x1054c4 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (xor_m16_r16_effect_step 0x1054c4 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x1054c9 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x1054c9) (movR32Imm32Effect 0x1054c9 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x1054c9 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x1054c9 0xbe (by decide) 0x8) pre_rip
  have f17 : InstrSpec 0x1054ce [0x4C, 0x89, 0xF7] (fun s => s.RIP = 0x1054ce) (movR64R64Effect 0x1054ce 7 14)
      [.gpr 14] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1054ce 7 14).toInstrSpec (mov_r64_r64_effect_step 0x1054ce 0x4c 0xf7 (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x1054d1 [0xE8, 0x3A, 0xB6, 0xFF, 0xFF] (PushPre 0x1054d1 5) (callEffect (fun _ => 0x100b10) 0x1054d6)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1054d1 0x100b10 0x1054d6).toInstrSpec (call_rel32_effect_step 0x1054d1 0xffffb63a (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105478) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.exec (n := 55) (ρ' := [(0, 53), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10547c) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 56) (RestInside.out (n := 56) f2 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 57) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105482) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 58) (RestInside.exec (n := 58) (ρ' := [(0, 56), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105487) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f4 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10548d) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.exec (n := 61) (ρ' := [(0, 59), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105492) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 62) (RestInside.out (n := 62) f6 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 63) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105498) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 64) (RestInside.exec (n := 64) (ρ' := [(0, 62), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10549d) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f8 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054a3) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 65), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054a8) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f10 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054ae) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.exec (n := 70) (ρ' := [(0, 68), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054b3) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054b9) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.exec (n := 73) (ρ' := [(0, 71), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054be) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f14 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054c4) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.exec (n := 76) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054c9) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 77) (RestInside.out (n := 77) f16 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 78) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (6, 77), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054ce) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 74), (3, 3), (4, 4), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054d1) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 74), (3, 3), (4, 81), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f18 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 83) (by decide) (by decide) rfl rfl

theorem block_l105472 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105472 :=
  Rest.liftedBlock (rest_l105472 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105472 x hx)

theorem rest_l1054d6_4 [Bindings] (code : CodeMap) :
    Rest (n := 203) code lifted (codeRange 0x1054d6 bytes_l1054d6) [(0, 151), (1, 197), (2, 201), (3, 3), (4, 4), (5, 147), (6, 108), (7, 199), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]
      12 0x105603 bytes_l1054d6_4 b_l1054d6_4 := by
  have f80 : InstrSpec 0x105603 [0x89, 0xF9] (fun s => s.RIP = 0x105603) (movR32R32Effect 0x105603 2 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105603 2 1 7).toInstrSpec (mov_r32_r32_effect_step 0x105603 0xf9 (by decide)) pre_rip
  have f81 : InstrSpec 0x105605 [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x105605) (rolR16Effect 0x105605 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x105605 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x105605 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f82 : InstrSpec 0x105609 [0x66, 0x42, 0x33, 0x4C, 0x63, 0x4A] (LoadPre 0x105609 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x4a)) s (0x105609 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105609 6 1 (.sib 3 (some 12) 1 (.d8 0x4a)))
      [.gpr 1, .gpr 3, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x105609 6 1 (.sib 3 (some 12) 1 (.d8 0x4a))).toInstrSpec (xor_r16_m16_rex_effect_step 0x105609 0x42 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x4a)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f83 : InstrSpec 0x10560f [0x31, 0xCA] (fun s => s.RIP = 0x10560f) (xorR32R32Effect 0x10560f 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10560f 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x10560f 0xca (by decide)) pre_rip
  have f84 : InstrSpec 0x105611 [0x66, 0x89, 0x54, 0x24, 0x0A] (StorePre 0x105611 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x105611 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105611 5 2 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105611 5 2 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m16_r16_effect_step 0x105611 2 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f85 : InstrSpec 0x105616 [0x66, 0x41, 0xC1, 0xC0, 0x08] (fun s => s.RIP = 0x105616) (rolR16Effect 0x105616 5 8 8)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (rolR16Effect_footprint 0x105616 5 8 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x105616 0x41 0xc0 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f86 : InstrSpec 0x10561b [0x66, 0x46, 0x33, 0x44, 0x63, 0x4C] (LoadPre 0x10561b (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x4c)) s (0x10561b + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x10561b 6 8 (.sib 3 (some 12) 1 (.d8 0x4c)))
      [.gpr 8, .gpr 3, .gpr 12] [] [.reg 8, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x10561b 6 8 (.sib 3 (some 12) 1 (.d8 0x4c))).toInstrSpec (xor_r16_m16_rex_effect_step 0x10561b 0x46 (by decide) 0 (.sib 3 (some 12) 1 (.d8 0x4c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f87 : InstrSpec 0x105621 [0x33, 0x7C, 0x24, 0x1C] (LoadPre 0x105621 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x105621 + BitVec.ofNat 64 4)) 4) (xorR32M32LowEffect 0x105621 7 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 7, .gpr 4] [] [.reg 7, .flags, .rip] :=
    (xorR32M32LowEffect_footprint 0x105621 7 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (xor_r32_m32_low_effect_step 0x105621 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f88 : InstrSpec 0x105625 [0x44, 0x31, 0xC7] (fun s => s.RIP = 0x105625) (xorR32R32Effect 0x105625 3 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105625 3 7 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x105625 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f89 : InstrSpec 0x105628 [0x66, 0x89, 0x7C, 0x24, 0x0C] (StorePre 0x105628 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105628 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105628 5 7 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105628 5 7 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x105628 7 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f90 : InstrSpec 0x10562d [0x49, 0x83, 0xC4, 0x20] (fun s => s.RIP = 0x10562d) (addR64Imm8Effect 0x10562d 12 0x20)
      [.gpr 12] [] [.reg 12, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x10562d 12 0x20).toInstrSpec (add_r64_imm8_effect_step 0x10562d 0x49 0xc4 0x20 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 203) (RestInside.out (n := 203) f80 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 204) (ρ' := [(0, 151), (1, 203), (2, 201), (3, 3), (4, 4), (5, 147), (6, 108), (7, 199), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105605) f80 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 205) (RestInside.out (n := 205) f81 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 206) (ρ' := [(0, 151), (1, 205), (2, 201), (3, 3), (4, 4), (5, 147), (6, 108), (7, 199), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105609) f81 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 207) (RestInside.out (n := 207) f82 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 208) (ρ' := [(0, 151), (1, 207), (2, 201), (3, 3), (4, 4), (5, 147), (6, 108), (7, 199), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10560f) f82 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 209) (RestInside.out (n := 209) f83 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 210) (ρ' := [(0, 151), (1, 207), (2, 209), (3, 3), (4, 4), (5, 147), (6, 108), (7, 199), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105611) f83 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 211) (RestInside.exec (n := 211) (ρ' := [(0, 151), (1, 207), (2, 209), (3, 3), (4, 4), (5, 147), (6, 108), (7, 199), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105616) f84 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 212) (RestInside.out (n := 212) f85 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 213) (ρ' := [(0, 151), (1, 207), (2, 209), (3, 3), (4, 4), (5, 147), (6, 108), (7, 199), (8, 212), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10561b) f85 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 214) (RestInside.out (n := 214) f86 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 215) (ρ' := [(0, 151), (1, 207), (2, 209), (3, 3), (4, 4), (5, 147), (6, 108), (7, 199), (8, 214), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105621) f86 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 216) (RestInside.out (n := 216) f87 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 217) (ρ' := [(0, 151), (1, 207), (2, 209), (3, 3), (4, 4), (5, 147), (6, 108), (7, 216), (8, 214), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105625) f87 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 218) (RestInside.out (n := 218) f88 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 219) (ρ' := [(0, 151), (1, 207), (2, 209), (3, 3), (4, 4), (5, 147), (6, 108), (7, 218), (8, 214), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105628) f88 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 220) (RestInside.exec (n := 220) (ρ' := [(0, 151), (1, 207), (2, 209), (3, 3), (4, 4), (5, 147), (6, 108), (7, 218), (8, 214), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10562d) f89 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 221) (RestInside.out (n := 221) f90 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 222) (ρ' := [(0, 151), (1, 207), (2, 209), (3, 3), (4, 4), (5, 147), (6, 108), (7, 218), (8, 214), (9, 192), (10, 153), (11, 165), (12, 221), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105631) f90 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact Rest.jmp (n := 223) (jmp_rel32_effect_step 0x105631 0xfffffb4a (by decide)) (List.cons_ne_nil _ _) (by decide) rfl

theorem rest_l1054d6_3 [Bindings] (code : CodeMap) :
    Rest (n := 167) code lifted (codeRange 0x1054d6 bytes_l1054d6) [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]
      32 0x1055ae bytes_l1054d6_3 b_l1054d6_3 := by
  have f60 : InstrSpec 0x1055ae [0x66, 0x44, 0x89, 0x5C, 0x24, 0x02] (StorePre 0x1055ae 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1055ae + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1055ae 6 11 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1055ae 6 11 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1055ae 0x44 (by decide) 3 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f61 : InstrSpec 0x1055b4 [0x66, 0x41, 0xC1, 0xC5, 0x08] (fun s => s.RIP = 0x1055b4) (rolR16Effect 0x1055b4 5 13 8)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR16Effect_footprint 0x1055b4 5 13 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x1055b4 0x41 0xc5 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x1055b9 [0x66, 0x46, 0x33, 0x6C, 0x63, 0x44] (LoadPre 0x1055b9 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x44)) s (0x1055b9 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1055b9 6 13 (.sib 3 (some 12) 1 (.d8 0x44)))
      [.gpr 13, .gpr 3, .gpr 12] [] [.reg 13, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1055b9 6 13 (.sib 3 (some 12) 1 (.d8 0x44))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1055b9 0x46 (by decide) 5 (.sib 3 (some 12) 1 (.d8 0x44)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f63 : InstrSpec 0x1055bf [0x44, 0x33, 0x74, 0x24, 0x18] (LoadPre 0x1055bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1055bf + BitVec.ofNat 64 5)) 4) (xorR32M32Effect 0x1055bf 14 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 14, .gpr 4] [] [.reg 14, .flags, .rip] :=
    (xorR32M32Effect_footprint 0x1055bf 14 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (xor_r32_m32_effect_step 0x1055bf 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f64 : InstrSpec 0x1055c4 [0x45, 0x31, 0xEE] (fun s => s.RIP = 0x1055c4) (xorR32R32Effect 0x1055c4 3 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1055c4 3 14 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x1055c4 0x45 0xee (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x1055c7 [0x66, 0x41, 0xC1, 0xC7, 0x08] (fun s => s.RIP = 0x1055c7) (rolR16Effect 0x1055c7 5 15 8)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR16Effect_footprint 0x1055c7 5 15 8).toInstrSpec (rol_r16_imm8_rex_effect_step 0x1055c7 0x41 0xc7 0x8 (by decide) (by decide) (by decide)) pre_rip
  have f66 : InstrSpec 0x1055cc [0x66, 0x44, 0x89, 0x74, 0x24, 0x04] (StorePre 0x1055cc 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1055cc + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1055cc 6 14 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 14, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1055cc 6 14 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1055cc 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f67 : InstrSpec 0x1055d2 [0x66, 0x46, 0x33, 0x7C, 0x63, 0x46] (LoadPre 0x1055d2 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x46)) s (0x1055d2 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1055d2 6 15 (.sib 3 (some 12) 1 (.d8 0x46)))
      [.gpr 15, .gpr 3, .gpr 12] [] [.reg 15, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1055d2 6 15 (.sib 3 (some 12) 1 (.d8 0x46))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1055d2 0x46 (by decide) 7 (.sib 3 (some 12) 1 (.d8 0x46)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f68 : InstrSpec 0x1055d8 [0x44, 0x31, 0xFA] (fun s => s.RIP = 0x1055d8) (xorR32R32Effect 0x1055d8 3 2 15)
      [.gpr 2, .gpr 15] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1055d8 3 2 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x1055d8 0x44 0xfa (by decide) (by decide)) pre_rip
  have f69 : InstrSpec 0x1055db [0x66, 0x89, 0x54, 0x24, 0x06] (StorePre 0x1055db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1055db + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1055db 5 2 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1055db 5 2 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (mov_m16_r16_effect_step 0x1055db 2 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f70 : InstrSpec 0x1055e0 [0x8B, 0x54, 0x24, 0x14] (LoadPre 0x1055e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1055e0 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1055e0 2 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1055e0 2 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_r32_m32_low_effect_step 0x1055e0 2 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f71 : InstrSpec 0x1055e4 [0x89, 0xD1] (fun s => s.RIP = 0x1055e4) (movR32R32Effect 0x1055e4 2 1 2)
      [.gpr 2] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1055e4 2 1 2).toInstrSpec (mov_r32_r32_effect_step 0x1055e4 0xd1 (by decide)) pre_rip
  have f72 : InstrSpec 0x1055e6 [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x1055e6) (rolR16Effect 0x1055e6 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x1055e6 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x1055e6 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f73 : InstrSpec 0x1055ea [0x66, 0x42, 0x33, 0x4C, 0x63, 0x48] (LoadPre 0x1055ea (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x48)) s (0x1055ea + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1055ea 6 1 (.sib 3 (some 12) 1 (.d8 0x48)))
      [.gpr 1, .gpr 3, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1055ea 6 1 (.sib 3 (some 12) 1 (.d8 0x48))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1055ea 0x42 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x48)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f74 : InstrSpec 0x1055f0 [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x1055f0) (xorR32R32Effect 0x1055f0 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1055f0 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x1055f0 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f75 : InstrSpec 0x1055f3 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x08] (StorePre 0x1055f3 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1055f3 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1055f3 6 9 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1055f3 6 9 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1055f3 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f76 : InstrSpec 0x1055f9 [0x89, 0xF9] (fun s => s.RIP = 0x1055f9) (movR32R32Effect 0x1055f9 2 1 7)
      [.gpr 7] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x1055f9 2 1 7).toInstrSpec (mov_r32_r32_effect_step 0x1055f9 0xf9 (by decide)) pre_rip
  have f77 : InstrSpec 0x1055fb [0x66, 0xC1, 0xC1, 0x0C] (fun s => s.RIP = 0x1055fb) (rolR16Effect 0x1055fb 4 1 12)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x1055fb 4 1 12).toInstrSpec (rol_r16_imm8_effect_step 0x1055fb 0xc1 0xc (by decide) (by decide)) pre_rip
  have f78 : InstrSpec 0x1055ff [0x31, 0xCF] (fun s => s.RIP = 0x1055ff) (xorR32R32Effect 0x1055ff 2 7 1)
      [.gpr 7, .gpr 1] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1055ff 2 7 1).toInstrSpec (xor_r32_r32_effect_step 0x1055ff 0xcf (by decide)) pre_rip
  have f79 : InstrSpec 0x105601 [0x31, 0xCA] (fun s => s.RIP = 0x105601) (xorR32R32Effect 0x105601 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105601 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x105601 0xca (by decide)) pre_rip
  refine Rest.ofInside (n := 167) (RestInside.exec (n := 167) (ρ' := [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055b4) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f61 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 168), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055b9) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f62 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055bf) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.out (n := 172) f63 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 173) (ρ' := [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 172), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055c4) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 174) (RestInside.out (n := 174) f64 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 175) (ρ' := [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055c7) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 176) (RestInside.out (n := 176) f65 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 177) (ρ' := [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055cc) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 178) (RestInside.exec (n := 178) (ρ' := [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 176), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055d2) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f67 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055d8) f67 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 181) (RestInside.out (n := 181) f68 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 182) (ρ' := [(0, 151), (1, 163), (2, 181), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055db) f68 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 183) (RestInside.exec (n := 183) (ρ' := [(0, 151), (1, 163), (2, 181), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055e0) f69 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 184) (RestInside.out (n := 184) f70 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 185) (ρ' := [(0, 151), (1, 163), (2, 184), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055e4) f70 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 186) (RestInside.out (n := 186) f71 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 187) (ρ' := [(0, 151), (1, 186), (2, 184), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055e6) f71 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 188) (RestInside.out (n := 188) f72 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 189) (ρ' := [(0, 151), (1, 188), (2, 184), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055ea) f72 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 190) (RestInside.out (n := 190) f73 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 191) (ρ' := [(0, 151), (1, 190), (2, 184), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055f0) f73 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 192) (RestInside.out (n := 192) f74 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 193) (ρ' := [(0, 151), (1, 190), (2, 184), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055f3) f74 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 194) (RestInside.exec (n := 194) (ρ' := [(0, 151), (1, 190), (2, 184), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055f9) f75 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 195) (RestInside.out (n := 195) f76 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 196) (ρ' := [(0, 151), (1, 195), (2, 184), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055fb) f76 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 197) (RestInside.out (n := 197) f77 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 198) (ρ' := [(0, 151), (1, 197), (2, 184), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055ff) f77 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 199) (RestInside.out (n := 199) f78 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 200) (ρ' := [(0, 151), (1, 197), (2, 184), (3, 3), (4, 4), (5, 147), (6, 108), (7, 199), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105601) f78 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 201) (RestInside.out (n := 201) f79 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 202) (ρ' := [(0, 151), (1, 197), (2, 201), (3, 3), (4, 4), (5, 147), (6, 108), (7, 199), (8, 121), (9, 192), (10, 153), (11, 165), (12, 117), (13, 170), (14, 174), (15, 179), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105603) f79 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1054d6_4 code

theorem rest_l1054d6_2 [Bindings] (code : CodeMap) :
    Rest (n := 129) code lifted (codeRange 0x1054d6 bytes_l1054d6) [(0, 123), (1, 110), (2, 104), (3, 3), (4, 4), (5, 119), (6, 108), (7, 125), (8, 121), (9, 106), (10, 61), (11, 127), (12, 117), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]
      52 0x105566 bytes_l1054d6_2 b_l1054d6_2 := by
  have f40 : InstrSpec 0x105566 [0x41, 0x89, 0xD5] (fun s => s.RIP = 0x105566) (movR32R32Effect 0x105566 3 13 2)
      [.gpr 2] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x105566 3 13 2).toInstrSpec (mov_r32_r32_rex_effect_step 0x105566 0x41 0xd5 (by decide) (by decide)) pre_rip
  have f41 : InstrSpec 0x105569 [0x31, 0xF2] (fun s => s.RIP = 0x105569) (xorR32R32Effect 0x105569 2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105569 2 2 6).toInstrSpec (xor_r32_r32_effect_step 0x105569 0xf2 (by decide)) pre_rip
  have f42 : InstrSpec 0x10556b [0x45, 0x89, 0xCF] (fun s => s.RIP = 0x10556b) (movR32R32Effect 0x10556b 3 15 9)
      [.gpr 9] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x10556b 3 15 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x10556b 0x45 0xcf (by decide) (by decide)) pre_rip
  have f43 : InstrSpec 0x10556e [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x10556e) (xorR32R32Effect 0x10556e 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10556e 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x10556e 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x105571 [0x66, 0xC1, 0xC7, 0x08] (fun s => s.RIP = 0x105571) (rolR16Effect 0x105571 4 7 8)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR16Effect_footprint 0x105571 4 7 8).toInstrSpec (rol_r16_imm8_effect_step 0x105571 0xc7 0x8 (by decide) (by decide)) pre_rip
  have f45 : InstrSpec 0x105575 [0x41, 0x31, 0xEA] (fun s => s.RIP = 0x105575) (xorR32R32Effect 0x105575 3 10 5)
      [.gpr 10, .gpr 5] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105575 3 10 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x105575 0x41 0xea (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x105578 [0x41, 0x31, 0xEB] (fun s => s.RIP = 0x105578) (xorR32R32Effect 0x105578 3 11 5)
      [.gpr 11, .gpr 5] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105578 3 11 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x105578 0x41 0xeb (by decide) (by decide)) pre_rip
  have f47 : InstrSpec 0x10557b [0x31, 0xEA] (fun s => s.RIP = 0x10557b) (xorR32R32Effect 0x10557b 2 2 5)
      [.gpr 2, .gpr 5] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10557b 2 2 5).toInstrSpec (xor_r32_r32_effect_step 0x10557b 0xea (by decide)) pre_rip
  have f48 : InstrSpec 0x10557d [0x41, 0x31, 0xE9] (fun s => s.RIP = 0x10557d) (xorR32R32Effect 0x10557d 3 9 5)
      [.gpr 9, .gpr 5] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10557d 3 9 5).toInstrSpec (xor_r32_r32_rex_effect_step 0x10557d 0x41 0xe9 (by decide) (by decide)) pre_rip
  have f49 : InstrSpec 0x105580 [0x66, 0xC1, 0xC5, 0x08] (fun s => s.RIP = 0x105580) (rolR16Effect 0x105580 4 5 8)
      [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 5, .flags, .rip] :=
    (rolR16Effect_footprint 0x105580 4 5 8).toInstrSpec (rol_r16_imm8_effect_step 0x105580 0xc5 0x8 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x105584 [0x66, 0x42, 0x33, 0x7C, 0x63, 0x40] (LoadPre 0x105584 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x40)) s (0x105584 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x105584 6 7 (.sib 3 (some 12) 1 (.d8 0x40)))
      [.gpr 7, .gpr 3, .gpr 12] [] [.reg 7, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x105584 6 7 (.sib 3 (some 12) 1 (.d8 0x40))).toInstrSpec (xor_r16_m16_rex_effect_step 0x105584 0x42 (by decide) 7 (.sib 3 (some 12) 1 (.d8 0x40)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f51 : InstrSpec 0x10558a [0x31, 0xE8] (fun s => s.RIP = 0x10558a) (xorR32R32Effect 0x10558a 2 0 5)
      [.gpr 0, .gpr 5] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10558a 2 0 5).toInstrSpec (xor_r32_r32_effect_step 0x10558a 0xe8 (by decide)) pre_rip
  have f52 : InstrSpec 0x10558c [0x41, 0x31, 0xFA] (fun s => s.RIP = 0x10558c) (xorR32R32Effect 0x10558c 3 10 7)
      [.gpr 10, .gpr 7] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10558c 3 10 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x10558c 0x41 0xfa (by decide) (by decide)) pre_rip
  have f53 : InstrSpec 0x10558f [0x0F, 0xB7, 0x7C, 0x24, 0x0A] (LoadPre 0x10558f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x10558f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10558f 5 7 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 4] [] [.reg 7, .rip] :=
    (movzxR32M16Effect_footprint 0x10558f 5 7 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (movzx_r32_m16_effect_step 0x10558f 7 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f54 : InstrSpec 0x105594 [0x66, 0x89, 0x44, 0x24, 0x0E] (StorePre 0x105594 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105594 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105594 5 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 0, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105594 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x105594 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f55 : InstrSpec 0x105599 [0x66, 0x44, 0x89, 0x14, 0x24] (StorePre 0x105599 5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105599 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105599 5 10 (.sib 4 none 0 .none))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105599 5 10 (.sib 4 none 0 .none)).toInstrSpec (mov_m16_r16_rex_effect_step 0x105599 0x44 (by decide) 2 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x10559e [0x44, 0x89, 0xF1] (fun s => s.RIP = 0x10559e) (movR32R32Effect 0x10559e 3 1 14)
      [.gpr 14] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10559e 3 1 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x10559e 0x44 0xf1 (by decide) (by decide)) pre_rip
  have f57 : InstrSpec 0x1055a1 [0x66, 0xC1, 0xC1, 0x08] (fun s => s.RIP = 0x1055a1) (rolR16Effect 0x1055a1 4 1 8)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x1055a1 4 1 8).toInstrSpec (rol_r16_imm8_effect_step 0x1055a1 0xc1 0x8 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x1055a5 [0x66, 0x42, 0x33, 0x4C, 0x63, 0x42] (LoadPre 0x1055a5 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x42)) s (0x1055a5 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x1055a5 6 1 (.sib 3 (some 12) 1 (.d8 0x42)))
      [.gpr 1, .gpr 3, .gpr 12] [] [.reg 1, .flags, .rip] :=
    (xorR16M16Effect_footprint 0x1055a5 6 1 (.sib 3 (some 12) 1 (.d8 0x42))).toInstrSpec (xor_r16_m16_rex_effect_step 0x1055a5 0x42 (by decide) 1 (.sib 3 (some 12) 1 (.d8 0x42)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f59 : InstrSpec 0x1055ab [0x41, 0x31, 0xCB] (fun s => s.RIP = 0x1055ab) (xorR32R32Effect 0x1055ab 3 11 1)
      [.gpr 11, .gpr 1] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1055ab 3 11 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x1055ab 0x41 0xcb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 129) (RestInside.out (n := 129) f40 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 130) (ρ' := [(0, 123), (1, 110), (2, 104), (3, 3), (4, 4), (5, 119), (6, 108), (7, 125), (8, 121), (9, 106), (10, 61), (11, 127), (12, 117), (13, 129), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105569) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 131) (RestInside.out (n := 131) f41 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 132) (ρ' := [(0, 123), (1, 110), (2, 131), (3, 3), (4, 4), (5, 119), (6, 108), (7, 125), (8, 121), (9, 106), (10, 61), (11, 127), (12, 117), (13, 129), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10556b) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 133) (RestInside.out (n := 133) f42 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 134) (ρ' := [(0, 123), (1, 110), (2, 131), (3, 3), (4, 4), (5, 119), (6, 108), (7, 125), (8, 121), (9, 106), (10, 61), (11, 127), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10556e) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 135) (RestInside.out (n := 135) f43 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 136) (ρ' := [(0, 123), (1, 110), (2, 131), (3, 3), (4, 4), (5, 119), (6, 108), (7, 125), (8, 121), (9, 135), (10, 61), (11, 127), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105571) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 137) (RestInside.out (n := 137) f44 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 138) (ρ' := [(0, 123), (1, 110), (2, 131), (3, 3), (4, 4), (5, 119), (6, 108), (7, 137), (8, 121), (9, 135), (10, 61), (11, 127), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105575) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 139) (RestInside.out (n := 139) f45 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 140) (ρ' := [(0, 123), (1, 110), (2, 131), (3, 3), (4, 4), (5, 119), (6, 108), (7, 137), (8, 121), (9, 135), (10, 139), (11, 127), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105578) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 141) (RestInside.out (n := 141) f46 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 142) (ρ' := [(0, 123), (1, 110), (2, 131), (3, 3), (4, 4), (5, 119), (6, 108), (7, 137), (8, 121), (9, 135), (10, 139), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10557b) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f47 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 123), (1, 110), (2, 143), (3, 3), (4, 4), (5, 119), (6, 108), (7, 137), (8, 121), (9, 135), (10, 139), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10557d) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f48 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 123), (1, 110), (2, 143), (3, 3), (4, 4), (5, 119), (6, 108), (7, 137), (8, 121), (9, 145), (10, 139), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105580) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f49 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 123), (1, 110), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 137), (8, 121), (9, 145), (10, 139), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105584) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f50 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 123), (1, 110), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 149), (8, 121), (9, 145), (10, 139), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10558a) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f51 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 151), (1, 110), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 149), (8, 121), (9, 145), (10, 139), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10558c) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f52 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 151), (1, 110), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 149), (8, 121), (9, 145), (10, 153), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10558f) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f53 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 151), (1, 110), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105594) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.exec (n := 157) (ρ' := [(0, 151), (1, 110), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105599) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 158) (RestInside.exec (n := 158) (ρ' := [(0, 151), (1, 110), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10559e) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 159) (RestInside.out (n := 159) f56 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 160) (ρ' := [(0, 151), (1, 159), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055a1) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 161) (RestInside.out (n := 161) f57 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 162) (ρ' := [(0, 151), (1, 161), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055a5) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 163) (RestInside.out (n := 163) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 164) (ρ' := [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 141), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055ab) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 165) (RestInside.out (n := 165) f59 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 166) (ρ' := [(0, 151), (1, 163), (2, 143), (3, 3), (4, 4), (5, 147), (6, 108), (7, 155), (8, 121), (9, 145), (10, 153), (11, 165), (12, 117), (13, 129), (14, 102), (15, 133), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1055ae) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1054d6_3 code

theorem rest_l1054d6_1 [Bindings] (code : CodeMap) :
    Rest (n := 92) code lifted (codeRange 0x1054d6 bytes_l1054d6) [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (7, 90), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]
      72 0x105527 bytes_l1054d6_1 b_l1054d6_1 := by
  have f20 : InstrSpec 0x105527 [0x4C, 0x89, 0x64, 0x24, 0x20] (StorePre 0x105527 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105527 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x105527 12 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 12, .gpr 4] [] [.rip] :=
    (movM64R64Effect_footprint 0x105527 12 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_m64_r64_effect_step 0x105527 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f21 : InstrSpec 0x10552c [0x41, 0x89, 0xFC] (fun s => s.RIP = 0x10552c) (movR32R32Effect 0x10552c 3 12 7)
      [.gpr 7] [] [.reg 12, .rip] :=
    (movR32R32Effect_footprint 0x10552c 3 12 7).toInstrSpec (mov_r32_r32_rex_effect_step 0x10552c 0x41 0xfc (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x10552f [0x89, 0x7C, 0x24, 0x1C] (StorePre 0x10552f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10552f + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10552f 7 (.sib 4 none 0 (.d8 0x1c)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x10552f 7 (.sib 4 none 0 (.d8 0x1c))).toInstrSpec (mov_m32_r32_low_effect_step 0x10552f 7 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f23 : InstrSpec 0x105533 [0x89, 0xEF] (fun s => s.RIP = 0x105533) (movR32R32Effect 0x105533 2 7 5)
      [.gpr 5] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x105533 2 7 5).toInstrSpec (mov_r32_r32_effect_step 0x105533 0xef (by decide)) pre_rip
  have f24 : InstrSpec 0x105535 [0x66, 0xC1, 0xC7, 0x0C] (fun s => s.RIP = 0x105535) (rolR16Effect 0x105535 4 7 12)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR16Effect_footprint 0x105535 4 7 12).toInstrSpec (rol_r16_imm8_effect_step 0x105535 0xc7 0xc (by decide) (by decide)) pre_rip
  have f25 : InstrSpec 0x105539 [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x105539) (xorR32R32Effect 0x105539 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105539 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x105539 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x10553c [0x45, 0x31, 0xEE] (fun s => s.RIP = 0x10553c) (xorR32R32Effect 0x10553c 3 14 13)
      [.gpr 14, .gpr 13] [] [.reg 14, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10553c 3 14 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x10553c 0x45 0xee (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x10553f [0x31, 0xF2] (fun s => s.RIP = 0x10553f) (xorR32R32Effect 0x10553f 2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10553f 2 2 6).toInstrSpec (xor_r32_r32_effect_step 0x10553f 0xf2 (by decide)) pre_rip
  have f28 : InstrSpec 0x105541 [0x41, 0x31, 0xC9] (fun s => s.RIP = 0x105541) (xorR32R32Effect 0x105541 3 9 1)
      [.gpr 9, .gpr 1] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105541 3 9 1).toInstrSpec (xor_r32_r32_rex_effect_step 0x105541 0x41 0xc9 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x105544 [0x89, 0xCE] (fun s => s.RIP = 0x105544) (movR32R32Effect 0x105544 2 6 1)
      [.gpr 1] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x105544 2 6 1).toInstrSpec (mov_r32_r32_effect_step 0x105544 0xce (by decide)) pre_rip
  have f30 : InstrSpec 0x105546 [0x44, 0x89, 0xF9] (fun s => s.RIP = 0x105546) (movR32R32Effect 0x105546 3 1 15)
      [.gpr 15] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x105546 3 1 15).toInstrSpec (mov_r32_r32_rex_effect_step 0x105546 0x44 0xf9 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x105549 [0x45, 0x31, 0xF8] (fun s => s.RIP = 0x105549) (xorR32R32Effect 0x105549 3 8 15)
      [.gpr 8, .gpr 15] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105549 3 8 15).toInstrSpec (xor_r32_r32_rex_effect_step 0x105549 0x45 0xf8 (by decide) (by decide)) pre_rip
  have f32 : InstrSpec 0x10554c [0x44, 0x89, 0x44, 0x24, 0x14] (StorePre 0x10554c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x10554c + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10554c 8 (.sib 4 none 0 (.d8 0x14)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM32R32Effect_footprint 0x10554c 8 (.sib 4 none 0 (.d8 0x14))).toInstrSpec (mov_m32_r32_effect_step 0x10554c 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x14)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f33 : InstrSpec 0x105551 [0x44, 0x31, 0xE0] (fun s => s.RIP = 0x105551) (xorR32R32Effect 0x105551 3 0 12)
      [.gpr 0, .gpr 12] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105551 3 0 12).toInstrSpec (xor_r32_r32_rex_effect_step 0x105551 0x44 0xe0 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x105554 [0x4C, 0x8B, 0x64, 0x24, 0x20] (LoadPre 0x105554 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x105554 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105554 12 (.sib 4 none 0 (.d8 0x20)))
      [.gpr 4] [] [.reg 12, .rip] :=
    (movR64M64Effect_footprint 0x105554 12 (.sib 4 none 0 (.d8 0x20))).toInstrSpec (mov_r64_m64_effect_step 0x105554 0x4c (by decide) 4 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f35 : InstrSpec 0x105559 [0x31, 0xFD] (fun s => s.RIP = 0x105559) (xorR32R32Effect 0x105559 2 5 7)
      [.gpr 5, .gpr 7] [] [.reg 5, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105559 2 5 7).toInstrSpec (xor_r32_r32_effect_step 0x105559 0xfd (by decide)) pre_rip
  have f36 : InstrSpec 0x10555b [0x41, 0x89, 0xC0] (fun s => s.RIP = 0x10555b) (movR32R32Effect 0x10555b 3 8 0)
      [.gpr 0] [] [.reg 8, .rip] :=
    (movR32R32Effect_footprint 0x10555b 3 8 0).toInstrSpec (mov_r32_r32_rex_effect_step 0x10555b 0x41 0xc0 (by decide) (by decide)) pre_rip
  have f37 : InstrSpec 0x10555e [0x31, 0xF8] (fun s => s.RIP = 0x10555e) (xorR32R32Effect 0x10555e 2 0 7)
      [.gpr 0, .gpr 7] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10555e 2 0 7).toInstrSpec (xor_r32_r32_effect_step 0x10555e 0xf8 (by decide)) pre_rip
  have f38 : InstrSpec 0x105560 [0x44, 0x89, 0xDF] (fun s => s.RIP = 0x105560) (movR32R32Effect 0x105560 3 7 11)
      [.gpr 11] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x105560 3 7 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x105560 0x44 0xdf (by decide) (by decide)) pre_rip
  have f39 : InstrSpec 0x105563 [0x45, 0x31, 0xEB] (fun s => s.RIP = 0x105563) (xorR32R32Effect 0x105563 3 11 13)
      [.gpr 11, .gpr 13] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105563 3 11 13).toInstrSpec (xor_r32_r32_rex_effect_step 0x105563 0x45 0xeb (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 92) (RestInside.exec (n := 92) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (7, 90), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10552c) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (7, 90), (8, 69), (9, 63), (10, 61), (11, 53), (12, 93), (13, 67), (14, 57), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10552f) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.exec (n := 95) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (7, 90), (8, 69), (9, 63), (10, 61), (11, 53), (12, 93), (13, 67), (14, 57), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105533) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 96) (RestInside.out (n := 96) f23 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 97) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (7, 96), (8, 69), (9, 63), (10, 61), (11, 53), (12, 93), (13, 67), (14, 57), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105535) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (7, 98), (8, 69), (9, 63), (10, 61), (11, 53), (12, 93), (13, 67), (14, 57), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105539) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (7, 98), (8, 69), (9, 63), (10, 61), (11, 100), (12, 93), (13, 67), (14, 57), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10553c) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (7, 98), (8, 69), (9, 63), (10, 61), (11, 100), (12, 93), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10553f) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 76), (1, 80), (2, 104), (3, 3), (4, 4), (5, 82), (6, 73), (7, 98), (8, 69), (9, 63), (10, 61), (11, 100), (12, 93), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105541) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 76), (1, 80), (2, 104), (3, 3), (4, 4), (5, 82), (6, 73), (7, 98), (8, 69), (9, 106), (10, 61), (11, 100), (12, 93), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105544) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 76), (1, 80), (2, 104), (3, 3), (4, 4), (5, 82), (6, 108), (7, 98), (8, 69), (9, 106), (10, 61), (11, 100), (12, 93), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105546) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 76), (1, 110), (2, 104), (3, 3), (4, 4), (5, 82), (6, 108), (7, 98), (8, 69), (9, 106), (10, 61), (11, 100), (12, 93), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105549) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.out (n := 112) f31 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 113) (ρ' := [(0, 76), (1, 110), (2, 104), (3, 3), (4, 4), (5, 82), (6, 108), (7, 98), (8, 112), (9, 106), (10, 61), (11, 100), (12, 93), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10554c) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 114) (RestInside.exec (n := 114) (ρ' := [(0, 76), (1, 110), (2, 104), (3, 3), (4, 4), (5, 82), (6, 108), (7, 98), (8, 112), (9, 106), (10, 61), (11, 100), (12, 93), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105551) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 115), (1, 110), (2, 104), (3, 3), (4, 4), (5, 82), (6, 108), (7, 98), (8, 112), (9, 106), (10, 61), (11, 100), (12, 93), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105554) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 115), (1, 110), (2, 104), (3, 3), (4, 4), (5, 82), (6, 108), (7, 98), (8, 112), (9, 106), (10, 61), (11, 100), (12, 117), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105559) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 115), (1, 110), (2, 104), (3, 3), (4, 4), (5, 119), (6, 108), (7, 98), (8, 112), (9, 106), (10, 61), (11, 100), (12, 117), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10555b) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 115), (1, 110), (2, 104), (3, 3), (4, 4), (5, 119), (6, 108), (7, 98), (8, 121), (9, 106), (10, 61), (11, 100), (12, 117), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10555e) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 123), (1, 110), (2, 104), (3, 3), (4, 4), (5, 119), (6, 108), (7, 98), (8, 121), (9, 106), (10, 61), (11, 100), (12, 117), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105560) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 123), (1, 110), (2, 104), (3, 3), (4, 4), (5, 119), (6, 108), (7, 125), (8, 121), (9, 106), (10, 61), (11, 100), (12, 117), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105563) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.out (n := 127) f39 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 128) (ρ' := [(0, 123), (1, 110), (2, 104), (3, 3), (4, 4), (5, 119), (6, 108), (7, 125), (8, 121), (9, 106), (10, 61), (11, 127), (12, 117), (13, 67), (14, 102), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105566) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1054d6_2 code

theorem rest_l1054d6 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1054d6 bytes_l1054d6) (entryMap (live .l1054d6))
      92 0x1054d6 bytes_l1054d6 b_l1054d6 := by
  have f0 : InstrSpec 0x1054d6 [0x44, 0x8B, 0x1C, 0x24] (LoadPre 0x1054d6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1054d6 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1054d6 11 (.sib 4 none 0 .none))
      [.gpr 4] [] [.reg 11, .rip] :=
    (movR32M32Effect_footprint 0x1054d6 11 (.sib 4 none 0 .none)).toInstrSpec (mov_r32_m32_effect_step 0x1054d6 0x44 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x1054da [0x8B, 0x54, 0x24, 0x04] (LoadPre 0x1054da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1054da + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1054da 2 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 4] [] [.reg 2, .rip] :=
    (movR32M32LowEffect_footprint 0x1054da 2 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_r32_m32_low_effect_step 0x1054da 2 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x1054de [0x44, 0x0F, 0xB7, 0x74, 0x24, 0x02] (LoadPre 0x1054de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1054de + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1054de 6 14 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 4] [] [.reg 14, .rip] :=
    (movzxR32M16Effect_footprint 0x1054de 6 14 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1054de 0x44 (by decide) 6 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f3 : InstrSpec 0x1054e4 [0x45, 0x89, 0xDA] (fun s => s.RIP = 0x1054e4) (movR32R32Effect 0x1054e4 3 10 11)
      [.gpr 11] [] [.reg 10, .rip] :=
    (movR32R32Effect_footprint 0x1054e4 3 10 11).toInstrSpec (mov_r32_r32_rex_effect_step 0x1054e4 0x45 0xda (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x1054e7 [0x66, 0x41, 0xC1, 0xC2, 0x0C] (fun s => s.RIP = 0x1054e7) (rolR16Effect 0x1054e7 5 10 12)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (rolR16Effect_footprint 0x1054e7 5 10 12).toInstrSpec (rol_r16_imm8_rex_effect_step 0x1054e7 0x41 0xc2 0xc (by decide) (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x1054ec [0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x06] (LoadPre 0x1054ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1054ec + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x1054ec 6 9 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 4] [] [.reg 9, .rip] :=
    (movzxR32M16Effect_footprint 0x1054ec 6 9 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (movzx_r32_m16_rex_effect_step 0x1054ec 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x1054f2 [0x45, 0x89, 0xF5] (fun s => s.RIP = 0x1054f2) (movR32R32Effect 0x1054f2 3 13 14)
      [.gpr 14] [] [.reg 13, .rip] :=
    (movR32R32Effect_footprint 0x1054f2 3 13 14).toInstrSpec (mov_r32_r32_rex_effect_step 0x1054f2 0x45 0xf5 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x1054f5 [0x66, 0x41, 0xC1, 0xC5, 0x0C] (fun s => s.RIP = 0x1054f5) (rolR16Effect 0x1054f5 5 13 12)
      [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 13, .flags, .rip] :=
    (rolR16Effect_footprint 0x1054f5 5 13 12).toInstrSpec (rol_r16_imm8_rex_effect_step 0x1054f5 0x41 0xc5 0xc (by decide) (by decide) (by decide)) pre_rip
  have f8 : InstrSpec 0x1054fa [0x44, 0x8B, 0x44, 0x24, 0x08] (LoadPre 0x1054fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1054fa + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1054fa 8 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 4] [] [.reg 8, .rip] :=
    (movR32M32Effect_footprint 0x1054fa 8 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_r32_m32_effect_step 0x1054fa 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f9 : InstrSpec 0x1054ff [0x89, 0xD6] (fun s => s.RIP = 0x1054ff) (movR32R32Effect 0x1054ff 2 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movR32R32Effect_footprint 0x1054ff 2 6 2).toInstrSpec (mov_r32_r32_effect_step 0x1054ff 0xd6 (by decide)) pre_rip
  have f10 : InstrSpec 0x105501 [0x66, 0xC1, 0xC6, 0x0C] (fun s => s.RIP = 0x105501) (rolR16Effect 0x105501 4 6 12)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (rolR16Effect_footprint 0x105501 4 6 12).toInstrSpec (rol_r16_imm8_effect_step 0x105501 0xc6 0xc (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x105505 [0x89, 0x74, 0x24, 0x18] (StorePre 0x105505 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x105505 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x105505 6 (.sib 4 none 0 (.d8 0x18)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM32R32LowEffect_footprint 0x105505 6 (.sib 4 none 0 (.d8 0x18))).toInstrSpec (mov_m32_r32_low_effect_step 0x105505 6 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f12 : InstrSpec 0x105509 [0x8B, 0x44, 0x24, 0x0C] (LoadPre 0x105509 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105509 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x105509 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 4] [] [.reg 0, .rip] :=
    (movR32M32LowEffect_footprint 0x105509 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_r32_m32_low_effect_step 0x105509 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f13 : InstrSpec 0x10550d [0x44, 0x89, 0xC9] (fun s => s.RIP = 0x10550d) (movR32R32Effect 0x10550d 3 1 9)
      [.gpr 9] [] [.reg 1, .rip] :=
    (movR32R32Effect_footprint 0x10550d 3 1 9).toInstrSpec (mov_r32_r32_rex_effect_step 0x10550d 0x44 0xc9 (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x105510 [0x66, 0xC1, 0xC1, 0x0C] (fun s => s.RIP = 0x105510) (rolR16Effect 0x105510 4 1 12)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (rolR16Effect_footprint 0x105510 4 1 12).toInstrSpec (rol_r16_imm8_effect_step 0x105510 0xc1 0xc (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x105514 [0x0F, 0xB7, 0x6C, 0x24, 0x0E] (LoadPre 0x105514 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105514 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105514 5 5 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 4] [] [.reg 5, .rip] :=
    (movzxR32M16Effect_footprint 0x105514 5 5 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (movzx_r32_m16_effect_step 0x105514 5 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x105519 [0x45, 0x89, 0xC7] (fun s => s.RIP = 0x105519) (movR32R32Effect 0x105519 3 15 8)
      [.gpr 8] [] [.reg 15, .rip] :=
    (movR32R32Effect_footprint 0x105519 3 15 8).toInstrSpec (mov_r32_r32_rex_effect_step 0x105519 0x45 0xc7 (by decide) (by decide)) pre_rip
  have f17 : InstrSpec 0x10551c [0x66, 0x41, 0xC1, 0xC7, 0x0C] (fun s => s.RIP = 0x10551c) (rolR16Effect 0x10551c 5 15 12)
      [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 15, .flags, .rip] :=
    (rolR16Effect_footprint 0x10551c 5 15 12).toInstrSpec (rol_r16_imm8_rex_effect_step 0x10551c 0x41 0xc7 0xc (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x105521 [0x89, 0xC7] (fun s => s.RIP = 0x105521) (movR32R32Effect 0x105521 2 7 0)
      [.gpr 0] [] [.reg 7, .rip] :=
    (movR32R32Effect_footprint 0x105521 2 7 0).toInstrSpec (mov_r32_r32_effect_step 0x105521 0xc7 (by decide)) pre_rip
  have f19 : InstrSpec 0x105523 [0x66, 0xC1, 0xC7, 0x0C] (fun s => s.RIP = 0x105523) (rolR16Effect 0x105523 4 7 12)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (rolR16Effect_footprint 0x105523 4 7 12).toInstrSpec (rol_r16_imm8_effect_step 0x105523 0xc7 0xc (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(3, 3), (4, 4), (11, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054da) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(2, 55), (3, 3), (4, 4), (11, 53), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054de) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(2, 55), (3, 3), (4, 4), (11, 53), (12, 12), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054e4) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(2, 55), (3, 3), (4, 4), (10, 59), (11, 53), (12, 12), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054e7) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(2, 55), (3, 3), (4, 4), (10, 61), (11, 53), (12, 12), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054ec) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(2, 55), (3, 3), (4, 4), (9, 63), (10, 61), (11, 53), (12, 12), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054f2) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(2, 55), (3, 3), (4, 4), (9, 63), (10, 61), (11, 53), (12, 12), (13, 65), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054f5) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f7 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(2, 55), (3, 3), (4, 4), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054fa) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f8 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 70) (ρ' := [(2, 55), (3, 3), (4, 4), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1054ff) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 71) (RestInside.out (n := 71) f9 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 72) (ρ' := [(2, 55), (3, 3), (4, 4), (6, 71), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105501) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f10 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(2, 55), (3, 3), (4, 4), (6, 73), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105505) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(2, 55), (3, 3), (4, 4), (6, 73), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105509) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (2, 55), (3, 3), (4, 4), (6, 73), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10550d) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 76), (1, 78), (2, 55), (3, 3), (4, 4), (6, 73), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105510) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (6, 73), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105514) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.out (n := 82) f15 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 83) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105519) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 84) (RestInside.out (n := 84) f16 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 85) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (15, 84), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10551c) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 86) (RestInside.out (n := 86) f17 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 87) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105521) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 88) (RestInside.out (n := 88) f18 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 89) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (7, 88), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105523) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 90) (RestInside.out (n := 90) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 91) (ρ' := [(0, 76), (1, 80), (2, 55), (3, 3), (4, 4), (5, 82), (6, 73), (7, 90), (8, 69), (9, 63), (10, 61), (11, 53), (12, 12), (13, 67), (14, 57), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105527) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l1054d6_1 code

theorem block_l1054d6 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1054d6 :=
  Rest.liftedBlock (rest_l1054d6 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1054d6 x hx)

theorem rest_l105636_3 [Bindings] (code : CodeMap) :
    Rest (n := 166) code lifted (codeRange 0x105636 bytes_l105636) [(0, 0), (1, 164), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      8 0x105719 bytes_l105636_3 b_l105636_3 := by
  have f60 : InstrSpec 0x105719 [0x31, 0xC8] (fun s => s.RIP = 0x105719) (xorR32R32Effect 0x105719 2 0 1)
      [.gpr 0, .gpr 1] [] [.reg 0, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105719 2 0 1).toInstrSpec (xor_r32_r32_effect_step 0x105719 0xc8 (by decide)) pre_rip
  have f61 : InstrSpec 0x10571b [0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10571b) (shlR32Effect 0x10571b 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shlR32Effect_footprint 0x10571b 3 1 2).toInstrSpec (shl_r32_imm8_effect_step 0x10571b 0xe1 0x2 (by decide) (by decide)) pre_rip
  have f62 : InstrSpec 0x10571e [0x31, 0xC1] (fun s => s.RIP = 0x10571e) (xorR32R32Effect 0x10571e 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10571e 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x10571e 0xc1 (by decide)) pre_rip
  have f63 : InstrSpec 0x105720 [0x66, 0x89, 0x4C, 0x24, 0x0E] (StorePre 0x105720 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105720 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105720 5 1 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 1, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105720 5 1 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (mov_m16_r16_effect_step 0x105720 1 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f64 : InstrSpec 0x105725 [0x49, 0x89, 0xE7] (fun s => s.RIP = 0x105725) (movR64R64Effect 0x105725 15 4)
      [.gpr 4] [] [.reg 15, .rip] :=
    (movR64R64Effect_footprint 0x105725 15 4).toInstrSpec (mov_r64_r64_effect_step 0x105725 0x49 0xe7 (by decide) (by decide)) pre_rip
  have f65 : InstrSpec 0x105728 [0xBE, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105728) (movR32Imm32Effect 0x105728 5 6 0x8)
      [] [] [.reg 6, .rip] :=
    (movR32Imm32Effect_footprint 0x105728 5 6 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x105728 0xbe (by decide) 0x8) pre_rip
  have f66 : InstrSpec 0x10572d [0x4C, 0x89, 0xFF] (fun s => s.RIP = 0x10572d) (movR64R64Effect 0x10572d 7 15)
      [.gpr 15] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x10572d 7 15).toInstrSpec (mov_r64_r64_effect_step 0x10572d 0x4c 0xff (by decide) (by decide)) pre_rip
  have f67 : InstrSpec 0x105730 [0xE8, 0xDB, 0xB3, 0xFF, 0xFF] (PushPre 0x105730 5) (callEffect (fun _ => 0x100b10) 0x105735)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x105730 0x100b10 0x105735).toInstrSpec (call_rel32_effect_step 0x105730 0xffffb3db (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 166) (RestInside.out (n := 166) f60 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 167) (ρ' := [(0, 166), (1, 164), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10571b) f60 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 168) (RestInside.out (n := 168) f61 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 169) (ρ' := [(0, 166), (1, 168), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10571e) f61 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 170) (RestInside.out (n := 170) f62 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 171) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105720) f62 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 172) (RestInside.exec (n := 172) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105725) f63 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 173) (RestInside.out (n := 173) f64 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 174) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (15, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105728) f64 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 175) (RestInside.out (n := 175) f65 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 176) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 4), (5, 5), (6, 175), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (15, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10572d) f65 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 177) (RestInside.out (n := 177) f66 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 178) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 4), (5, 5), (6, 175), (7, 177), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (15, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105730) f66 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 179) (RestInside.out (n := 179) f67 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 180) (ρ' := [(0, 166), (1, 170), (2, 155), (3, 3), (4, 179), (5, 5), (6, 175), (7, 177), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (15, 173), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x100b10) f67 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 181) (by decide) (by decide) rfl rfl

theorem rest_l105636_2 [Bindings] (code : CodeMap) :
    Rest (n := 128) code lifted (codeRange 0x105636 bytes_l105636) [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 121), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      28 0x1056d7 bytes_l105636_2 b_l105636_2 := by
  have f40 : InstrSpec 0x1056d7 [0x0F, 0xB7, 0xF2] (fun s => s.RIP = 0x1056d7) (movzxR32R16Effect 0x1056d7 3 6 2)
      [.gpr 2] [] [.reg 6, .rip] :=
    (movzxR32R16Effect_footprint 0x1056d7 3 6 2).toInstrSpec (movzx_r32_r16_effect_step 0x1056d7 0xf2 (by decide)) pre_rip
  have f41 : InstrSpec 0x1056da [0xC1, 0xEE, 0x02] (fun s => s.RIP = 0x1056da) (shrR32Effect 0x1056da 3 6 2)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shrR32Effect_footprint 0x1056da 3 6 2).toInstrSpec (shr_r32_imm8_effect_step 0x1056da 0xee 0x2 (by decide) (by decide)) pre_rip
  have f42 : InstrSpec 0x1056dd [0x31, 0xD6] (fun s => s.RIP = 0x1056dd) (xorR32R32Effect 0x1056dd 2 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056dd 2 6 2).toInstrSpec (xor_r32_r32_effect_step 0x1056dd 0xd6 (by decide)) pre_rip
  have f43 : InstrSpec 0x1056df [0x81, 0xE6, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x1056df) (andR32Imm32Effect 0x1056df 6 6 0x3030)
      [.gpr 6] [] [.reg 6, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1056df 6 6 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x1056df 0xe6 0x3030 (by decide) (by decide)) pre_rip
  have f44 : InstrSpec 0x1056e5 [0x31, 0xF2] (fun s => s.RIP = 0x1056e5) (xorR32R32Effect 0x1056e5 2 2 6)
      [.gpr 2, .gpr 6] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056e5 2 2 6).toInstrSpec (xor_r32_r32_effect_step 0x1056e5 0xf2 (by decide)) pre_rip
  have f45 : InstrSpec 0x1056e7 [0xC1, 0xE6, 0x02] (fun s => s.RIP = 0x1056e7) (shlR32Effect 0x1056e7 3 6 2)
      [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 6, .flags, .rip] :=
    (shlR32Effect_footprint 0x1056e7 3 6 2).toInstrSpec (shl_r32_imm8_effect_step 0x1056e7 0xe6 0x2 (by decide) (by decide)) pre_rip
  have f46 : InstrSpec 0x1056ea [0x31, 0xD6] (fun s => s.RIP = 0x1056ea) (xorR32R32Effect 0x1056ea 2 6 2)
      [.gpr 6, .gpr 2] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056ea 2 6 2).toInstrSpec (xor_r32_r32_effect_step 0x1056ea 0xd6 (by decide)) pre_rip
  have f47 : InstrSpec 0x1056ec [0x66, 0x89, 0x74, 0x24, 0x0A] (StorePre 0x1056ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x1056ec + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1056ec 5 6 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 6, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1056ec 5 6 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (mov_m16_r16_effect_step 0x1056ec 6 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f48 : InstrSpec 0x1056f1 [0x0F, 0xB7, 0xD1] (fun s => s.RIP = 0x1056f1) (movzxR32R16Effect 0x1056f1 3 2 1)
      [.gpr 1] [] [.reg 2, .rip] :=
    (movzxR32R16Effect_footprint 0x1056f1 3 2 1).toInstrSpec (movzx_r32_r16_effect_step 0x1056f1 0xd1 (by decide)) pre_rip
  have f49 : InstrSpec 0x1056f4 [0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x1056f4) (shrR32Effect 0x1056f4 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shrR32Effect_footprint 0x1056f4 3 2 2).toInstrSpec (shr_r32_imm8_effect_step 0x1056f4 0xea 0x2 (by decide) (by decide)) pre_rip
  have f50 : InstrSpec 0x1056f7 [0x31, 0xCA] (fun s => s.RIP = 0x1056f7) (xorR32R32Effect 0x1056f7 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056f7 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x1056f7 0xca (by decide)) pre_rip
  have f51 : InstrSpec 0x1056f9 [0x81, 0xE2, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x1056f9) (andR32Imm32Effect 0x1056f9 6 2 0x3030)
      [.gpr 2] [] [.reg 2, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1056f9 6 2 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x1056f9 0xe2 0x3030 (by decide) (by decide)) pre_rip
  have f52 : InstrSpec 0x1056ff [0x31, 0xD1] (fun s => s.RIP = 0x1056ff) (xorR32R32Effect 0x1056ff 2 1 2)
      [.gpr 1, .gpr 2] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056ff 2 1 2).toInstrSpec (xor_r32_r32_effect_step 0x1056ff 0xd1 (by decide)) pre_rip
  have f53 : InstrSpec 0x105701 [0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x105701) (shlR32Effect 0x105701 3 2 2)
      [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 2, .flags, .rip] :=
    (shlR32Effect_footprint 0x105701 3 2 2).toInstrSpec (shl_r32_imm8_effect_step 0x105701 0xe2 0x2 (by decide) (by decide)) pre_rip
  have f54 : InstrSpec 0x105704 [0x31, 0xCA] (fun s => s.RIP = 0x105704) (xorR32R32Effect 0x105704 2 2 1)
      [.gpr 2, .gpr 1] [] [.reg 2, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105704 2 2 1).toInstrSpec (xor_r32_r32_effect_step 0x105704 0xca (by decide)) pre_rip
  have f55 : InstrSpec 0x105706 [0x66, 0x89, 0x54, 0x24, 0x0C] (StorePre 0x105706 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105706 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105706 5 2 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 2, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105706 5 2 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (mov_m16_r16_effect_step 0x105706 2 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f56 : InstrSpec 0x10570b [0x0F, 0xB7, 0xC8] (fun s => s.RIP = 0x10570b) (movzxR32R16Effect 0x10570b 3 1 0)
      [.gpr 0] [] [.reg 1, .rip] :=
    (movzxR32R16Effect_footprint 0x10570b 3 1 0).toInstrSpec (movzx_r32_r16_effect_step 0x10570b 0xc8 (by decide)) pre_rip
  have f57 : InstrSpec 0x10570e [0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10570e) (shrR32Effect 0x10570e 3 1 2)
      [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 1, .flags, .rip] :=
    (shrR32Effect_footprint 0x10570e 3 1 2).toInstrSpec (shr_r32_imm8_effect_step 0x10570e 0xe9 0x2 (by decide) (by decide)) pre_rip
  have f58 : InstrSpec 0x105711 [0x31, 0xC1] (fun s => s.RIP = 0x105711) (xorR32R32Effect 0x105711 2 1 0)
      [.gpr 1, .gpr 0] [] [.reg 1, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105711 2 1 0).toInstrSpec (xor_r32_r32_effect_step 0x105711 0xc1 (by decide)) pre_rip
  have f59 : InstrSpec 0x105713 [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105713) (andR32Imm32Effect 0x105713 6 1 0x3030)
      [.gpr 1] [] [.reg 1, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105713 6 1 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x105713 0xe1 0x3030 (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 128) (RestInside.out (n := 128) f40 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 129) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 128), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056da) f40 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 130) (RestInside.out (n := 130) f41 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 131) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 130), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056dd) f41 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 132) (RestInside.out (n := 132) f42 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 133) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 132), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056df) f42 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 134) (RestInside.out (n := 134) f43 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 135) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 134), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056e5) f43 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 136) (RestInside.out (n := 136) f44 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 137) (ρ' := [(0, 0), (1, 1), (2, 136), (3, 3), (4, 4), (5, 5), (6, 134), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056e7) f44 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 138) (RestInside.out (n := 138) f45 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 139) (ρ' := [(0, 0), (1, 1), (2, 136), (3, 3), (4, 4), (5, 5), (6, 138), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056ea) f45 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 140) (RestInside.out (n := 140) f46 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 141) (ρ' := [(0, 0), (1, 1), (2, 136), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056ec) f46 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 142) (RestInside.exec (n := 142) (ρ' := [(0, 0), (1, 1), (2, 136), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056f1) f47 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 143) (RestInside.out (n := 143) f48 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 144) (ρ' := [(0, 0), (1, 1), (2, 143), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056f4) f48 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 145) (RestInside.out (n := 145) f49 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 146) (ρ' := [(0, 0), (1, 1), (2, 145), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056f7) f49 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 147) (RestInside.out (n := 147) f50 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 148) (ρ' := [(0, 0), (1, 1), (2, 147), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056f9) f50 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 149) (RestInside.out (n := 149) f51 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 150) (ρ' := [(0, 0), (1, 1), (2, 149), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056ff) f51 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 151) (RestInside.out (n := 151) f52 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 152) (ρ' := [(0, 0), (1, 151), (2, 149), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105701) f52 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 153) (RestInside.out (n := 153) f53 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 154) (ρ' := [(0, 0), (1, 151), (2, 153), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105704) f53 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 155) (RestInside.out (n := 155) f54 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 156) (ρ' := [(0, 0), (1, 151), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105706) f54 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 157) (RestInside.exec (n := 157) (ρ' := [(0, 0), (1, 151), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10570b) f55 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 158) (RestInside.out (n := 158) f56 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 159) (ρ' := [(0, 0), (1, 158), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10570e) f56 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 160) (RestInside.out (n := 160) f57 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 161) (ρ' := [(0, 0), (1, 160), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105711) f57 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 162) (RestInside.out (n := 162) f58 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 163) (ρ' := [(0, 0), (1, 162), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105713) f58 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 164) (RestInside.out (n := 164) f59 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 165) (ρ' := [(0, 0), (1, 164), (2, 155), (3, 3), (4, 4), (5, 5), (6, 140), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105719) f59 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l105636_3 code

theorem rest_l105636_1 [Bindings] (code : CodeMap) :
    Rest (n := 91) code lifted (codeRange 0x105636 bytes_l105636) [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 89), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]
      48 0x10568b bytes_l105636_1 b_l105636_1 := by
  have f20 : InstrSpec 0x10568b [0x45, 0x31, 0xC8] (fun s => s.RIP = 0x10568b) (xorR32R32Effect 0x10568b 3 8 9)
      [.gpr 8, .gpr 9] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10568b 3 8 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10568b 0x45 0xc8 (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x10568e [0x41, 0xC1, 0xE1, 0x02] (fun s => s.RIP = 0x10568e) (shlR32Effect 0x10568e 4 9 2)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shlR32Effect_footprint 0x10568e 4 9 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10568e 0x41 0xe1 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f22 : InstrSpec 0x105692 [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x105692) (xorR32R32Effect 0x105692 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105692 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x105692 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f23 : InstrSpec 0x105695 [0x66, 0x44, 0x89, 0x4C, 0x24, 0x04] (StorePre 0x105695 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x105695 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x105695 6 9 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 9, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105695 6 9 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (mov_m16_r16_rex_effect_step 0x105695 0x44 (by decide) 1 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f24 : InstrSpec 0x10569b [0x44, 0x0F, 0xB7, 0xC7] (fun s => s.RIP = 0x10569b) (movzxR32R16Effect 0x10569b 4 8 7)
      [.gpr 7] [] [.reg 8, .rip] :=
    (movzxR32R16Effect_footprint 0x10569b 4 8 7).toInstrSpec (movzx_r32_r16_rex_effect_step 0x10569b 0x44 (by decide) 0xc7 (by decide)) pre_rip
  have f25 : InstrSpec 0x10569f [0x41, 0xC1, 0xE8, 0x02] (fun s => s.RIP = 0x10569f) (shrR32Effect 0x10569f 4 8 2)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shrR32Effect_footprint 0x10569f 4 8 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10569f 0x41 0xe8 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f26 : InstrSpec 0x1056a3 [0x41, 0x31, 0xF8] (fun s => s.RIP = 0x1056a3) (xorR32R32Effect 0x1056a3 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056a3 3 8 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x1056a3 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f27 : InstrSpec 0x1056a6 [0x41, 0x81, 0xE0, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x1056a6) (andR32Imm32Effect 0x1056a6 7 8 0x3030)
      [.gpr 8] [] [.reg 8, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1056a6 7 8 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x1056a6 0x41 0xe0 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f28 : InstrSpec 0x1056ad [0x44, 0x31, 0xC7] (fun s => s.RIP = 0x1056ad) (xorR32R32Effect 0x1056ad 3 7 8)
      [.gpr 7, .gpr 8] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056ad 3 7 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x1056ad 0x44 0xc7 (by decide) (by decide)) pre_rip
  have f29 : InstrSpec 0x1056b0 [0x41, 0xC1, 0xE0, 0x02] (fun s => s.RIP = 0x1056b0) (shlR32Effect 0x1056b0 4 8 2)
      [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 8, .flags, .rip] :=
    (shlR32Effect_footprint 0x1056b0 4 8 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x1056b0 0x41 0xe0 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f30 : InstrSpec 0x1056b4 [0x41, 0x31, 0xF8] (fun s => s.RIP = 0x1056b4) (xorR32R32Effect 0x1056b4 3 8 7)
      [.gpr 8, .gpr 7] [] [.reg 8, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056b4 3 8 7).toInstrSpec (xor_r32_r32_rex_effect_step 0x1056b4 0x41 0xf8 (by decide) (by decide)) pre_rip
  have f31 : InstrSpec 0x1056b7 [0x66, 0x44, 0x89, 0x44, 0x24, 0x06] (StorePre 0x1056b7 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1056b7 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1056b7 6 8 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 8, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1056b7 6 8 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (mov_m16_r16_rex_effect_step 0x1056b7 0x44 (by decide) 0 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f32 : InstrSpec 0x1056bd [0x0F, 0xB7, 0xFE] (fun s => s.RIP = 0x1056bd) (movzxR32R16Effect 0x1056bd 3 7 6)
      [.gpr 6] [] [.reg 7, .rip] :=
    (movzxR32R16Effect_footprint 0x1056bd 3 7 6).toInstrSpec (movzx_r32_r16_effect_step 0x1056bd 0xfe (by decide)) pre_rip
  have f33 : InstrSpec 0x1056c0 [0xC1, 0xEF, 0x02] (fun s => s.RIP = 0x1056c0) (shrR32Effect 0x1056c0 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shrR32Effect_footprint 0x1056c0 3 7 2).toInstrSpec (shr_r32_imm8_effect_step 0x1056c0 0xef 0x2 (by decide) (by decide)) pre_rip
  have f34 : InstrSpec 0x1056c3 [0x31, 0xF7] (fun s => s.RIP = 0x1056c3) (xorR32R32Effect 0x1056c3 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056c3 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x1056c3 0xf7 (by decide)) pre_rip
  have f35 : InstrSpec 0x1056c5 [0x81, 0xE7, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x1056c5) (andR32Imm32Effect 0x1056c5 6 7 0x3030)
      [.gpr 7] [] [.reg 7, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x1056c5 6 7 0x3030).toInstrSpec (and_r32_imm32_effect_step 0x1056c5 0xe7 0x3030 (by decide) (by decide)) pre_rip
  have f36 : InstrSpec 0x1056cb [0x31, 0xFE] (fun s => s.RIP = 0x1056cb) (xorR32R32Effect 0x1056cb 2 6 7)
      [.gpr 6, .gpr 7] [] [.reg 6, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056cb 2 6 7).toInstrSpec (xor_r32_r32_effect_step 0x1056cb 0xfe (by decide)) pre_rip
  have f37 : InstrSpec 0x1056cd [0xC1, 0xE7, 0x02] (fun s => s.RIP = 0x1056cd) (shlR32Effect 0x1056cd 3 7 2)
      [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 7, .flags, .rip] :=
    (shlR32Effect_footprint 0x1056cd 3 7 2).toInstrSpec (shl_r32_imm8_effect_step 0x1056cd 0xe7 0x2 (by decide) (by decide)) pre_rip
  have f38 : InstrSpec 0x1056d0 [0x31, 0xF7] (fun s => s.RIP = 0x1056d0) (xorR32R32Effect 0x1056d0 2 7 6)
      [.gpr 7, .gpr 6] [] [.reg 7, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x1056d0 2 7 6).toInstrSpec (xor_r32_r32_effect_step 0x1056d0 0xf7 (by decide)) pre_rip
  have f39 : InstrSpec 0x1056d2 [0x66, 0x89, 0x7C, 0x24, 0x08] (StorePre 0x1056d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1056d2 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1056d2 5 7 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 7, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x1056d2 5 7 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (mov_m16_r16_effect_step 0x1056d2 7 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  refine Rest.ofInside (n := 91) (RestInside.out (n := 91) f20 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 92) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 91), (9, 89), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10568e) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 93) (RestInside.out (n := 93) f21 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 94) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 91), (9, 93), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105692) f21 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 95) (RestInside.out (n := 95) f22 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 96) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 91), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105695) f22 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 97) (RestInside.exec (n := 97) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 91), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10569b) f23 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 98) (RestInside.out (n := 98) f24 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 99) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 98), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10569f) f24 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 100) (RestInside.out (n := 100) f25 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 101) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 100), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056a3) f25 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 102) (RestInside.out (n := 102) f26 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 103) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 102), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056a6) f26 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 104) (RestInside.out (n := 104) f27 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 105) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 104), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056ad) f27 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 106) (RestInside.out (n := 106) f28 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 107) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 106), (8, 104), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056b0) f28 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 108) (RestInside.out (n := 108) f29 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 109) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 106), (8, 108), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056b4) f29 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 110) (RestInside.out (n := 110) f30 (.reg (.gpr 8)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 111) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 106), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056b7) f30 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 112) (RestInside.exec (n := 112) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 106), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056bd) f31 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 113) (RestInside.out (n := 113) f32 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 114) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 113), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056c0) f32 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 115) (RestInside.out (n := 115) f33 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 116) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 115), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056c3) f33 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 117) (RestInside.out (n := 117) f34 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 118) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 117), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056c5) f34 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 119) (RestInside.out (n := 119) f35 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 120) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 119), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056cb) f35 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 121) (RestInside.out (n := 121) f36 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 122) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 121), (7, 119), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056cd) f36 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 123) (RestInside.out (n := 123) f37 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 124) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 121), (7, 123), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056d0) f37 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 125) (RestInside.out (n := 125) f38 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 126) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 121), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056d2) f38 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 127) (RestInside.exec (n := 127) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 121), (7, 125), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1056d7) f39 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  exact rest_l105636_2 code

theorem rest_l105636 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105636 bytes_l105636) (entryMap (live .l105636))
      68 0x105636 bytes_l105636 b_l105636 := by
  have f0 : InstrSpec 0x105636 [0x45, 0x0F, 0xB7, 0xDA] (fun s => s.RIP = 0x105636) (movzxR32R16Effect 0x105636 4 11 10)
      [.gpr 10] [] [.reg 11, .rip] :=
    (movzxR32R16Effect_footprint 0x105636 4 11 10).toInstrSpec (movzx_r32_r16_rex_effect_step 0x105636 0x45 (by decide) 0xda (by decide)) pre_rip
  have f1 : InstrSpec 0x10563a [0x41, 0xC1, 0xEB, 0x02] (fun s => s.RIP = 0x10563a) (shrR32Effect 0x10563a 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shrR32Effect_footprint 0x10563a 4 11 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10563a 0x41 0xeb 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x10563e [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x10563e) (xorR32R32Effect 0x10563e 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10563e 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10563e 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f3 : InstrSpec 0x105641 [0x41, 0x81, 0xE3, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105641) (andR32Imm32Effect 0x105641 7 11 0x3030)
      [.gpr 11] [] [.reg 11, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105641 7 11 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x105641 0x41 0xe3 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f4 : InstrSpec 0x105648 [0x45, 0x31, 0xDA] (fun s => s.RIP = 0x105648) (xorR32R32Effect 0x105648 3 10 11)
      [.gpr 10, .gpr 11] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105648 3 10 11).toInstrSpec (xor_r32_r32_rex_effect_step 0x105648 0x45 0xda (by decide) (by decide)) pre_rip
  have f5 : InstrSpec 0x10564b [0x41, 0xC1, 0xE3, 0x02] (fun s => s.RIP = 0x10564b) (shlR32Effect 0x10564b 4 11 2)
      [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 11, .flags, .rip] :=
    (shlR32Effect_footprint 0x10564b 4 11 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10564b 0x41 0xe3 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f6 : InstrSpec 0x10564f [0x45, 0x31, 0xD3] (fun s => s.RIP = 0x10564f) (xorR32R32Effect 0x10564f 3 11 10)
      [.gpr 11, .gpr 10] [] [.reg 11, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10564f 3 11 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x10564f 0x45 0xd3 (by decide) (by decide)) pre_rip
  have f7 : InstrSpec 0x105652 [0x66, 0x44, 0x89, 0x1C, 0x24] (StorePre 0x105652 5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105652 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105652 5 11 (.sib 4 none 0 .none))
      [.gpr 11, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105652 5 11 (.sib 4 none 0 .none)).toInstrSpec (mov_m16_r16_rex_effect_step 0x105652 0x44 (by decide) 3 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f8 : InstrSpec 0x105657 [0x45, 0x0F, 0xB7, 0xD1] (fun s => s.RIP = 0x105657) (movzxR32R16Effect 0x105657 4 10 9)
      [.gpr 9] [] [.reg 10, .rip] :=
    (movzxR32R16Effect_footprint 0x105657 4 10 9).toInstrSpec (movzx_r32_r16_rex_effect_step 0x105657 0x45 (by decide) 0xd1 (by decide)) pre_rip
  have f9 : InstrSpec 0x10565b [0x41, 0xC1, 0xEA, 0x02] (fun s => s.RIP = 0x10565b) (shrR32Effect 0x10565b 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shrR32Effect_footprint 0x10565b 4 10 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10565b 0x41 0xea 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f10 : InstrSpec 0x10565f [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x10565f) (xorR32R32Effect 0x10565f 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x10565f 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x10565f 0x45 0xca (by decide) (by decide)) pre_rip
  have f11 : InstrSpec 0x105662 [0x41, 0x81, 0xE2, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105662) (andR32Imm32Effect 0x105662 7 10 0x3030)
      [.gpr 10] [] [.reg 10, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105662 7 10 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x105662 0x41 0xe2 0x3030 (by decide) (by decide) (by decide)) pre_rip
  have f12 : InstrSpec 0x105669 [0x45, 0x31, 0xD1] (fun s => s.RIP = 0x105669) (xorR32R32Effect 0x105669 3 9 10)
      [.gpr 9, .gpr 10] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105669 3 9 10).toInstrSpec (xor_r32_r32_rex_effect_step 0x105669 0x45 0xd1 (by decide) (by decide)) pre_rip
  have f13 : InstrSpec 0x10566c [0x41, 0xC1, 0xE2, 0x02] (fun s => s.RIP = 0x10566c) (shlR32Effect 0x10566c 4 10 2)
      [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 10, .flags, .rip] :=
    (shlR32Effect_footprint 0x10566c 4 10 2).toInstrSpec (shl_r32_imm8_rex_effect_step 0x10566c 0x41 0xe2 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f14 : InstrSpec 0x105670 [0x45, 0x31, 0xCA] (fun s => s.RIP = 0x105670) (xorR32R32Effect 0x105670 3 10 9)
      [.gpr 10, .gpr 9] [] [.reg 10, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105670 3 10 9).toInstrSpec (xor_r32_r32_rex_effect_step 0x105670 0x45 0xca (by decide) (by decide)) pre_rip
  have f15 : InstrSpec 0x105673 [0x66, 0x44, 0x89, 0x54, 0x24, 0x02] (StorePre 0x105673 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x105673 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x105673 6 10 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 10, .gpr 4] [] [.rip] :=
    (movM16R16Effect_footprint 0x105673 6 10 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (mov_m16_r16_rex_effect_step 0x105673 0x44 (by decide) 2 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f16 : InstrSpec 0x105679 [0x45, 0x0F, 0xB7, 0xC8] (fun s => s.RIP = 0x105679) (movzxR32R16Effect 0x105679 4 9 8)
      [.gpr 8] [] [.reg 9, .rip] :=
    (movzxR32R16Effect_footprint 0x105679 4 9 8).toInstrSpec (movzx_r32_r16_rex_effect_step 0x105679 0x45 (by decide) 0xc8 (by decide)) pre_rip
  have f17 : InstrSpec 0x10567d [0x41, 0xC1, 0xE9, 0x02] (fun s => s.RIP = 0x10567d) (shrR32Effect 0x10567d 4 9 2)
      [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [] [.reg 9, .flags, .rip] :=
    (shrR32Effect_footprint 0x10567d 4 9 2).toInstrSpec (shr_r32_imm8_rex_effect_step 0x10567d 0x41 0xe9 0x2 (by decide) (by decide) (by decide)) pre_rip
  have f18 : InstrSpec 0x105681 [0x45, 0x31, 0xC1] (fun s => s.RIP = 0x105681) (xorR32R32Effect 0x105681 3 9 8)
      [.gpr 9, .gpr 8] [] [.reg 9, .flags, .rip] :=
    (xorR32R32Effect_footprint 0x105681 3 9 8).toInstrSpec (xor_r32_r32_rex_effect_step 0x105681 0x45 0xc1 (by decide) (by decide)) pre_rip
  have f19 : InstrSpec 0x105684 [0x41, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] (fun s => s.RIP = 0x105684) (andR32Imm32Effect 0x105684 7 9 0x3030)
      [.gpr 9] [] [.reg 9, .flags, .rip] :=
    (andR32Imm32Effect_footprint 0x105684 7 9 0x3030).toInstrSpec (and_r32_imm32_rex_effect_step 0x105684 0x41 0xe1 0x3030 (by decide) (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10563a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 55), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10563e) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 58) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 57), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105641) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 59) (RestInside.out (n := 59) f3 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 60) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 59), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105648) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f4 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 59), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10564b) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f5 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 64) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 63), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10564f) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 65) (RestInside.out (n := 65) f6 (.reg (.gpr 11)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 66) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105652) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 67) (RestInside.exec (n := 67) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105657) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 68) (RestInside.out (n := 68) f8 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 69) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 68), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10565b) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f9 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 70), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10565f) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f10 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 73) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 72), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105662) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 74) (RestInside.out (n := 74) f11 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 75) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 74), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105669) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f12 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 76), (10, 74), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10566c) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.out (n := 78) f13 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 79) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 76), (10, 78), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105670) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 80) (RestInside.out (n := 80) f14 (.reg (.gpr 10)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 81) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 76), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105673) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 82) (RestInside.exec (n := 82) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 76), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105679) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f16 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 83), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10567d) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f17 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 85), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105681) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f18 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 87), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105684) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 89) (RestInside.out (n := 89) f19 (.reg (.gpr 9)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 90) (ρ' := [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 89), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10568b) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l105636_1 code

theorem block_l105636 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105636 :=
  Rest.liftedBlock (rest_l105636 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105636 x hx)

theorem rest_l105735_1 [Bindings] (code : CodeMap) :
    Rest (n := 85) code lifted (codeRange 0x105735 bytes_l105735) [(0, 76), (1, 53), (2, 79), (3, 81), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]
      2 0x1057a6 bytes_l105735_1 b_l105735_1 := by
  have f20 : InstrSpec 0x1057a6 [0x4C, 0x89, 0xFE] (fun s => s.RIP = 0x1057a6) (movR64R64Effect 0x1057a6 6 15)
      [.gpr 15] [] [.reg 6, .rip] :=
    (movR64R64Effect_footprint 0x1057a6 6 15).toInstrSpec (mov_r64_r64_effect_step 0x1057a6 0x4c 0xfe (by decide) (by decide)) pre_rip
  have f21 : InstrSpec 0x1057a9 [0xE8, 0xE2, 0x45, 0x00, 0x00] (PushPre 0x1057a9 5) (callEffect (fun _ => 0x109d90) 0x1057ae)
      [.gpr 4] [] [.reg 4, .rip] :=
    (callEffect_footprint 0x1057a9 0x109d90 0x1057ae).toInstrSpec (call_rel32_effect_step 0x1057a9 0x45e2 (by decide)) (StorePre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 85) (RestInside.out (n := 85) f20 (.reg (.gpr 6)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 86) (ρ' := [(0, 76), (1, 53), (2, 79), (3, 81), (4, 4), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057a9) f20 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 87) (RestInside.out (n := 87) f21 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 88) (ρ' := [(0, 76), (1, 53), (2, 79), (3, 81), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x109d90) f21 (fun _ _ => rfl) (.inl rfl) rfl rfl ?_
  exact Rest.call (n := 89) (by decide) (by decide) rfl rfl

theorem rest_l105735 [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x105735 bytes_l105735) (entryMap (live .l105735))
      22 0x105735 bytes_l105735 b_l105735 := by
  have f0 : InstrSpec 0x105735 [0x48, 0x8B, 0x4C, 0x24, 0x28] (LoadPre 0x105735 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105735 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105735 1 (.sib 4 none 0 (.d8 0x28)))
      [.gpr 4] [] [.reg 1, .rip] :=
    (movR64M64Effect_footprint 0x105735 1 (.sib 4 none 0 (.d8 0x28))).toInstrSpec (mov_r64_m64_effect_step 0x105735 0x48 (by decide) 1 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f1 : InstrSpec 0x10573a [0x0F, 0xB7, 0x81, 0xA0, 0x00, 0x00, 0x00] (LoadPre 0x10573a (fun s => AddrMode.addr (.base 1 (.d32 0xa0)) s (0x10573a + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x10573a 7 0 (.base 1 (.d32 0xa0)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10573a 7 0 (.base 1 (.d32 0xa0))).toInstrSpec (movzx_r32_m16_effect_step 0x10573a 0 (.base 1 (.d32 0xa0)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f2 : InstrSpec 0x105741 [0x66, 0x31, 0x04, 0x24] (StorePre 0x105741 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105741 + BitVec.ofNat 64 4)) 2) (xorMREffect 0x105741 4 16 0 (.sib 4 none 0 .none))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105741 4 0 (.sib 4 none 0 .none)).toInstrSpec (xor_m16_r16_effect_step 0x105741 0 (.sib 4 none 0 .none) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f3 : InstrSpec 0x105745 [0x0F, 0xB7, 0x81, 0xA2, 0x00, 0x00, 0x00] (LoadPre 0x105745 (fun s => AddrMode.addr (.base 1 (.d32 0xa2)) s (0x105745 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x105745 7 0 (.base 1 (.d32 0xa2)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105745 7 0 (.base 1 (.d32 0xa2))).toInstrSpec (movzx_r32_m16_effect_step 0x105745 0 (.base 1 (.d32 0xa2)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f4 : InstrSpec 0x10574c [0x66, 0x31, 0x44, 0x24, 0x02] (StorePre 0x10574c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x10574c + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10574c 5 16 0 (.sib 4 none 0 (.d8 0x2)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x10574c 5 0 (.sib 4 none 0 (.d8 0x2))).toInstrSpec (xor_m16_r16_effect_step 0x10574c 0 (.sib 4 none 0 (.d8 0x2)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f5 : InstrSpec 0x105751 [0x0F, 0xB7, 0x81, 0xA4, 0x00, 0x00, 0x00] (LoadPre 0x105751 (fun s => AddrMode.addr (.base 1 (.d32 0xa4)) s (0x105751 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x105751 7 0 (.base 1 (.d32 0xa4)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105751 7 0 (.base 1 (.d32 0xa4))).toInstrSpec (movzx_r32_m16_effect_step 0x105751 0 (.base 1 (.d32 0xa4)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f6 : InstrSpec 0x105758 [0x66, 0x31, 0x44, 0x24, 0x04] (StorePre 0x105758 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x105758 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105758 5 16 0 (.sib 4 none 0 (.d8 0x4)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105758 5 0 (.sib 4 none 0 (.d8 0x4))).toInstrSpec (xor_m16_r16_effect_step 0x105758 0 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f7 : InstrSpec 0x10575d [0x0F, 0xB7, 0x81, 0xA6, 0x00, 0x00, 0x00] (LoadPre 0x10575d (fun s => AddrMode.addr (.base 1 (.d32 0xa6)) s (0x10575d + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x10575d 7 0 (.base 1 (.d32 0xa6)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10575d 7 0 (.base 1 (.d32 0xa6))).toInstrSpec (movzx_r32_m16_effect_step 0x10575d 0 (.base 1 (.d32 0xa6)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f8 : InstrSpec 0x105764 [0x66, 0x31, 0x44, 0x24, 0x06] (StorePre 0x105764 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x105764 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105764 5 16 0 (.sib 4 none 0 (.d8 0x6)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105764 5 0 (.sib 4 none 0 (.d8 0x6))).toInstrSpec (xor_m16_r16_effect_step 0x105764 0 (.sib 4 none 0 (.d8 0x6)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f9 : InstrSpec 0x105769 [0x0F, 0xB7, 0x81, 0xA8, 0x00, 0x00, 0x00] (LoadPre 0x105769 (fun s => AddrMode.addr (.base 1 (.d32 0xa8)) s (0x105769 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x105769 7 0 (.base 1 (.d32 0xa8)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105769 7 0 (.base 1 (.d32 0xa8))).toInstrSpec (movzx_r32_m16_effect_step 0x105769 0 (.base 1 (.d32 0xa8)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f10 : InstrSpec 0x105770 [0x66, 0x31, 0x44, 0x24, 0x08] (StorePre 0x105770 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105770 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105770 5 16 0 (.sib 4 none 0 (.d8 0x8)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105770 5 0 (.sib 4 none 0 (.d8 0x8))).toInstrSpec (xor_m16_r16_effect_step 0x105770 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f11 : InstrSpec 0x105775 [0x0F, 0xB7, 0x81, 0xAA, 0x00, 0x00, 0x00] (LoadPre 0x105775 (fun s => AddrMode.addr (.base 1 (.d32 0xaa)) s (0x105775 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x105775 7 0 (.base 1 (.d32 0xaa)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105775 7 0 (.base 1 (.d32 0xaa))).toInstrSpec (movzx_r32_m16_effect_step 0x105775 0 (.base 1 (.d32 0xaa)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f12 : InstrSpec 0x10577c [0x66, 0x31, 0x44, 0x24, 0x0A] (StorePre 0x10577c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x10577c + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10577c 5 16 0 (.sib 4 none 0 (.d8 0xa)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x10577c 5 0 (.sib 4 none 0 (.d8 0xa))).toInstrSpec (xor_m16_r16_effect_step 0x10577c 0 (.sib 4 none 0 (.d8 0xa)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f13 : InstrSpec 0x105781 [0x0F, 0xB7, 0x81, 0xAC, 0x00, 0x00, 0x00] (LoadPre 0x105781 (fun s => AddrMode.addr (.base 1 (.d32 0xac)) s (0x105781 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x105781 7 0 (.base 1 (.d32 0xac)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x105781 7 0 (.base 1 (.d32 0xac))).toInstrSpec (movzx_r32_m16_effect_step 0x105781 0 (.base 1 (.d32 0xac)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f14 : InstrSpec 0x105788 [0x66, 0x31, 0x44, 0x24, 0x0C] (StorePre 0x105788 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105788 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105788 5 16 0 (.sib 4 none 0 (.d8 0xc)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105788 5 0 (.sib 4 none 0 (.d8 0xc))).toInstrSpec (xor_m16_r16_effect_step 0x105788 0 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f15 : InstrSpec 0x10578d [0x0F, 0xB7, 0x81, 0xAE, 0x00, 0x00, 0x00] (LoadPre 0x10578d (fun s => AddrMode.addr (.base 1 (.d32 0xae)) s (0x10578d + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x10578d 7 0 (.base 1 (.d32 0xae)))
      [.gpr 1] [] [.reg 0, .rip] :=
    (movzxR32M16Effect_footprint 0x10578d 7 0 (.base 1 (.d32 0xae))).toInstrSpec (movzx_r32_m16_effect_step 0x10578d 0 (.base 1 (.d32 0xae)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f16 : InstrSpec 0x105794 [0x66, 0x31, 0x44, 0x24, 0x0E] (StorePre 0x105794 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105794 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105794 5 16 0 (.sib 4 none 0 (.d8 0xe)))
      [.gpr 0, .gpr 4] [] [.flags, .rip] :=
    (xorMREffect16_footprint 0x105794 5 0 (.sib 4 none 0 (.d8 0xe))).toInstrSpec (xor_m16_r16_effect_step 0x105794 0 (.sib 4 none 0 (.d8 0xe)) (by decide) (by decide) (by decide)) (StorePre.of_addr rfl)
  have f17 : InstrSpec 0x105799 [0xBA, 0x08, 0x00, 0x00, 0x00] (fun s => s.RIP = 0x105799) (movR32Imm32Effect 0x105799 5 2 0x8)
      [] [] [.reg 2, .rip] :=
    (movR32Imm32Effect_footprint 0x105799 5 2 0x8).toInstrSpec (mov_r32_imm32_effect_step 0x105799 0xba (by decide) 0x8) pre_rip
  have f18 : InstrSpec 0x10579e [0x48, 0x8B, 0x5C, 0x24, 0x30] (LoadPre 0x10579e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10579e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10579e 3 (.sib 4 none 0 (.d8 0x30)))
      [.gpr 4] [] [.reg 3, .rip] :=
    (movR64M64Effect_footprint 0x10579e 3 (.sib 4 none 0 (.d8 0x30))).toInstrSpec (mov_r64_m64_effect_step 0x10579e 0x48 (by decide) 3 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide)) (LoadPre.of_addr rfl)
  have f19 : InstrSpec 0x1057a3 [0x48, 0x89, 0xDF] (fun s => s.RIP = 0x1057a3) (movR64R64Effect 0x1057a3 7 3)
      [.gpr 3] [] [.reg 7, .rip] :=
    (movR64R64Effect_footprint 0x1057a3 7 3).toInstrSpec (mov_r64_r64_effect_step 0x1057a3 0x48 0xdf (by decide) (by decide)) pre_rip
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 1)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10573a) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 55), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105741) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.exec (n := 57) (ρ' := [(0, 55), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105745) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 58) (RestInside.out (n := 58) f3 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 59) (ρ' := [(0, 58), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10574c) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.exec (n := 60) (ρ' := [(0, 58), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105751) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 61) (RestInside.out (n := 61) f5 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 62) (ρ' := [(0, 61), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105758) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.exec (n := 63) (ρ' := [(0, 61), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10575d) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 64) (RestInside.out (n := 64) f7 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 65) (ρ' := [(0, 64), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105764) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.exec (n := 66) (ρ' := [(0, 64), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105769) f8 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 67) (RestInside.out (n := 67) f9 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 68) (ρ' := [(0, 67), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105770) f9 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.exec (n := 69) (ρ' := [(0, 67), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105775) f10 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 70) (RestInside.out (n := 70) f11 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 71) (ρ' := [(0, 70), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10577c) f11 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.exec (n := 72) (ρ' := [(0, 70), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105781) f12 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 73) (RestInside.out (n := 73) f13 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 74) (ρ' := [(0, 73), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105788) f13 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.exec (n := 75) (ρ' := [(0, 73), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10578d) f14 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 76) (RestInside.out (n := 76) f15 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 77) (ρ' := [(0, 76), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105794) f15 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 78) (RestInside.exec (n := 78) (ρ' := [(0, 76), (1, 53), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x105799) f16 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_) (List.cons_ne_nil _ _)
  refine Rest.ofInside (n := 79) (RestInside.out (n := 79) f17 (.reg (.gpr 2)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 80) (ρ' := [(0, 76), (1, 53), (2, 79), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x10579e) f17 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 81) (RestInside.out (n := 81) f18 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 82) (ρ' := [(0, 76), (1, 53), (2, 79), (3, 81), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057a3) f18 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 83) (RestInside.out (n := 83) f19 (.reg (.gpr 7)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 84) (ρ' := [(0, 76), (1, 53), (2, 79), (3, 81), (4, 4), (5, 5), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057a6) f19 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  exact rest_l105735_1 code

theorem block_l105735 [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l105735 :=
  Rest.liftedBlock (rest_l105735 code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l105735 x hx)

theorem rest_l1057ae [Bindings] (code : CodeMap) :
    Rest (n := 53) code lifted (codeRange 0x1057ae bytes_l1057ae) (entryMap (live .l1057ae))
      9 0x1057ae bytes_l1057ae b_l1057ae := by
  have f0 : InstrSpec 0x1057ae [0x48, 0x89, 0xD8] (fun s => s.RIP = 0x1057ae) (movR64R64Effect 0x1057ae 0 3)
      [.gpr 3] [] [.reg 0, .rip] :=
    (movR64R64Effect_footprint 0x1057ae 0 3).toInstrSpec (mov_r64_r64_effect_step 0x1057ae 0x48 0xd8 (by decide) (by decide)) pre_rip
  have f1 : InstrSpec 0x1057b1 [0x48, 0x83, 0xC4, 0x38] (fun s => s.RIP = 0x1057b1) (addR64Imm8Effect 0x1057b1 4 0x38)
      [.gpr 4] [] [.reg 4, .flags, .rip] :=
    (addR64Imm8Effect_footprint 0x1057b1 4 0x38).toInstrSpec (add_r64_imm8_effect_step 0x1057b1 0x48 0xc4 0x38 (by decide) (by decide) (by decide)) pre_rip
  have f2 : InstrSpec 0x1057b5 [0x5B] (PopPre 0x1057b5) (popR64Effect 0x1057b5 1 3)
      [.gpr 4] [] [.reg 3, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1057b5 1 3).toInstrSpec (pop_r64_effect_step 0x1057b5 0x5b (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f3 : InstrSpec 0x1057b6 [0x41, 0x5C] (PopPre 0x1057b6) (popR64Effect 0x1057b6 2 12)
      [.gpr 4] [] [.reg 12, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1057b6 2 12).toInstrSpec (pop_r64_rex_effect_step 0x1057b6 0x41 0x5c (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f4 : InstrSpec 0x1057b8 [0x41, 0x5D] (PopPre 0x1057b8) (popR64Effect 0x1057b8 2 13)
      [.gpr 4] [] [.reg 13, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1057b8 2 13).toInstrSpec (pop_r64_rex_effect_step 0x1057b8 0x41 0x5d (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f5 : InstrSpec 0x1057ba [0x41, 0x5E] (PopPre 0x1057ba) (popR64Effect 0x1057ba 2 14)
      [.gpr 4] [] [.reg 14, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1057ba 2 14).toInstrSpec (pop_r64_rex_effect_step 0x1057ba 0x41 0x5e (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f6 : InstrSpec 0x1057bc [0x41, 0x5F] (PopPre 0x1057bc) (popR64Effect 0x1057bc 2 15)
      [.gpr 4] [] [.reg 15, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1057bc 2 15).toInstrSpec (pop_r64_rex_effect_step 0x1057bc 0x41 0x5f (by decide) (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f7 : InstrSpec 0x1057be [0x5D] (PopPre 0x1057be) (popR64Effect 0x1057be 1 5)
      [.gpr 4] [] [.reg 5, .reg 4, .rip] :=
    (popR64Effect_footprint 0x1057be 1 5).toInstrSpec (pop_r64_effect_step 0x1057be 0x5d (by decide) (by decide)) (LoadPre.of_stateOf (by lift_reads))
  have f8 : InstrSpec 0x1057bf [0xC3] (RetPre 0x1057bf) (retEffect)
      [.gpr 4] [] [.reg 4, .rip] :=
    (retEffect_footprint 0x1057bf).toInstrSpec (ret_effect_step 0x1057bf) (RetPre.of_stateOf (by lift_reads))
  refine Rest.ofInside (n := 53) (RestInside.out (n := 53) f0 (.reg (.gpr 0)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 54) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057b1) f0 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 55) (RestInside.out (n := 55) f1 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.exec (n := 56) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 3), (4, 55), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057b5) f1 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 57) (RestInside.out (n := 57) f2 (.reg (.gpr 3)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 58) f2 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 59) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 58), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057b6) f2 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 60) (RestInside.out (n := 60) f3 (.reg (.gpr 12)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 61) f3 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 62) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 61), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057b8) f3 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 63) (RestInside.out (n := 63) f4 (.reg (.gpr 13)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 64) f4 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 65) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057ba) f4 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 66) (RestInside.out (n := 66) f5 (.reg (.gpr 14)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 67) f5 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 68) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057bc) f5 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 69) (RestInside.out (n := 69) f6 (.reg (.gpr 15)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 70) f6 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 71) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057be) f6 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 72) (RestInside.out (n := 72) f7 (.reg (.gpr 5)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 73) f7 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  refine RestInside.exec (n := 74) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) (p' := 0x1057bf) f7 (fun _ _ => rfl) (.inr (by decide)) rfl rfl ?_
  refine Rest.ofInside (n := 75) (RestInside.out (n := 75) f8 (.target) trivial (fun h => nomatch h) rfl ?_) (List.cons_ne_nil _ _)
  refine RestInside.out (n := 76) f8 (.reg (.gpr 4)) ⟨rfl, by decide, by decide⟩ (fun h => nomatch h) rfl ?_
  exact RestInside.ret (n := 77) (ρ' := [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)]) f8 (by decide) rfl rfl rfl (by decide)

theorem block_l1057ae [Bindings] (code : CodeMap) (hcode : ∀ x ∈ fnCode, x ∈ code) :
    LiftedBlock code lifted .l1057ae :=
  Rest.liftedBlock (rest_l1057ae code) (List.cons_ne_nil _ _) fun x hx => hcode x (code_l1057ae x hx)

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

theorem_by block_l105100_eval :
    program.runBlock (dialect code) ⟨.l105100, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105134_eval :
    program.runBlock (dialect code) ⟨.l105134, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105180_eval :
    program.runBlock (dialect code) ⟨.l105180, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1051a0_eval :
    program.runBlock (dialect code) ⟨.l1051a0, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1051a8_eval :
    program.runBlock (dialect code) ⟨.l1051a8, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105236_eval :
    program.runBlock (dialect code) ⟨.l105236, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105243_eval :
    program.runBlock (dialect code) ⟨.l105243, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l10546a_eval :
    program.runBlock (dialect code) ⟨.l10546a, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105472_eval :
    program.runBlock (dialect code) ⟨.l105472, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1054d6_eval :
    program.runBlock (dialect code) ⟨.l1054d6, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105636_eval :
    program.runBlock (dialect code) ⟨.l105636, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l105735_eval :
    program.runBlock (dialect code) ⟨.l105735, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem_by block_l1057ae_eval :
    program.runBlock (dialect code) ⟨.l1057ae, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

end Steps

end AesGcm.Proofs.Machine.LIR
