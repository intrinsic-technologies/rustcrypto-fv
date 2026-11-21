import P256.Proofs.EcdhWrapper.Peer.Buffer.Memory
import P256.Proofs.EcdhWrapper.Peer.Buffer.Model

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Buffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Curve.LinearCombination.NafReverse
open P256.Proofs.Sec1.Decode.Prepare.Copy

set_option maxHeartbeats 1800000 in
theorem run [Bindings] {initial s0 : RamState} {secret peer : ByteArray} {slices : Array Input}
    {f : Nat → UInt8} (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬InProgram (returnBoundary initial).rip) (ready0 : ReadyToStep s0)
    (loaded0 : ProgramLoaded s0)
    (grow0 : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s0.external[a]?).isSome)
    (sp0 : stackPtr s0=stackPtr initial-504) (rip : s0.RIP=0x106a3d)
    (w0 : Window s0 f 305) :
    ∃ t, Advances (returnBoundary initial) 45 s0 t ∧ ReadyToStep t ∧
      ProgramLoaded t ∧ Window t (copiedWindow f) 305 ∧
      t.RIP=0x106b70 ∧ AgreesExcept (components (stackPtr s0)) s0 t := by
  obtain ⟨s1,a1,ready1,e1⟩ := (movzx_r32_m16_effect_step 0x106a3d 0 (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl).advances ready0
    (programText_slice (programLoaded_codeIn loaded0) 0x6a3d _ (by decide) (by decide +kernel))
    ⟨rip,readable call grow0 sp0 (off := 168) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a45 (by decide)))
  have g1 : AgreesExcept [.reg 0,.rip] s0 s1 := e1.agrees
  have wide1 : AgreesExcept (components (stackPtr s0)) s0 s1 := g1.mono (by simp [components])
  have w1 : Window s1 f 305 := window_registers w0 g1 (by simp) (by simp [Component.Covers])
  have v1 : s1.regValue .rax = (memLoad s0.external (stackPtr s0+168) 16).setWidth 64 := e1.writes
  have sp1 : stackPtr s1=stackPtr initial-504 := (g1.read (n := 64) (r := 4) (by simp)).trans sp0
  have loaded1 := loaded_after call loaded0 sp0 wide1
  have grow1 := fun a h ↦ g1.grow a (grow0 a h)
  have same1 : stackPtr s1=stackPtr s0 := sp1.trans sp0.symm
  have total1 : AgreesExcept (components (stackPtr s0)) s0 s1 := wide1
  obtain ⟨s2,a2,ready2,e2⟩ := (mov_m16_r16_effect_step 0x106a45 0 (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl).advances ready1
    (programText_slice (programLoaded_codeIn loaded1) 0x6a45 _ (by decide) (by decide +kernel))
    ⟨e1.rip,writable call grow1 sp1 (off := 240) (by decide) (by decide),code_apart call sp1 (off := 240) (len := 2) (pc := 0x6a45) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a4d (by decide)))
  have g2 : AgreesExcept [.mem (stackPtr s1+240) 2,.rip] s1 s2 := by
    have h := e2.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide2 := store_agrees g2 (by decide)
  have value2 : memLoad s2.external (stackPtr s1+240) 16 =
      memLoad s0.external (stackPtr s0+168) 16 := by
    have h : memLoad s2.external (stackPtr s1+240) 16 = (s1.regValue .rax).setWidth 16 := e2.writes
    have reg : s1.regValue .rax = (memLoad s0.external (stackPtr s0+168) 16).setWidth 64 := v1
    rw [h,reg]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 16≤64),BitVec.setWidth_eq]
  let f2 := update f (fun j ↦ f (168+j)) 240 2
  have w2 : Window s2 f2 305 := window_store_bounded (by decide) w1 w0
    (by decide) (by decide) g2 value2
  have sp2 : stackPtr s2=stackPtr initial-504 := (g2.read (n := 64) (r := 4) (by simp)).trans sp1
  have loaded2 := loaded_after call loaded1 sp1 wide2
  have grow2 := fun a h ↦ g2.grow a (grow1 a h)
  have same2 : stackPtr s2=stackPtr s0 := sp2.trans sp0.symm
  have total2 : AgreesExcept (components (stackPtr s0)) s0 s2 := by
    rw [same1] at wide2
    exact (total1.trans wide2).mono (by simp)
  obtain ⟨s3,a3,ready3,e3⟩ := (movzx_r32_m8_effect_step 0x106a4d 0 (.sib 4 none 0 (.d32 170)) (by decide) rfl rfl).advances ready2
    (programText_slice (programLoaded_codeIn loaded2) 0x6a4d _ (by decide) (by decide +kernel))
    ⟨e2.rip,readable call grow2 sp2 (off := 170) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a55 (by decide)))
  have g3 : AgreesExcept [.reg 0,.rip] s2 s3 := e3.agrees
  have wide3 : AgreesExcept (components (stackPtr s2)) s2 s3 := g3.mono (by simp [components])
  have w3 : Window s3 f2 305 := window_registers w2 g3 (by simp) (by simp [Component.Covers])
  have v3 : s3.regValue .rax = (memLoad s2.external (stackPtr s2+170) 8).setWidth 64 := e3.writes
  have sp3 : stackPtr s3=stackPtr initial-504 := (g3.read (n := 64) (r := 4) (by simp)).trans sp2
  have loaded3 := loaded_after call loaded2 sp2 wide3
  have grow3 := fun a h ↦ g3.grow a (grow2 a h)
  have same3 : stackPtr s3=stackPtr s0 := sp3.trans sp0.symm
  have total3 : AgreesExcept (components (stackPtr s0)) s0 s3 := by
    rw [same2] at wide3
    exact (total2.trans wide3).mono (by simp)
  obtain ⟨s4,a4,ready4,e4⟩ := (mov_m8_r8_legacy_effect_step 0x106a55 0 (by decide) (.sib 4 none 0 (.d32 242)) (by decide) rfl rfl).advances ready3
    (programText_slice (programLoaded_codeIn loaded3) 0x6a55 _ (by decide) (by decide +kernel))
    ⟨e3.rip,byte_writable call grow3 sp3 (off := 242) (by decide),code_apart call sp3 (off := 242) (len := 1) (pc := 0x6a55) (n := 7) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a5c (by decide)))
  have g4 : AgreesExcept [.mem (stackPtr s3+242) 1,.rip] s3 s4 := by
    have h := e4.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide4 := store_agrees g4 (by decide)
  have value4 : memLoad s4.external (stackPtr s3+242) 8 =
      memLoad s2.external (stackPtr s2+170) 8 := by
    have h : memLoad s4.external (stackPtr s3+242) 8 = (s3.regValue .rax).setWidth 8 := e4.writes
    have reg : s3.regValue .rax = (memLoad s2.external (stackPtr s2+170) 8).setWidth 64 := v3
    rw [h,reg]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 8≤64),BitVec.setWidth_eq]
  let f4 := update f2 (fun j ↦ f2 (170+j)) 242 1
  have w4 : Window s4 f4 305 := window_store_bounded (by decide) w3 w2
    (by decide) (by decide) g4 value4
  have sp4 : stackPtr s4=stackPtr initial-504 := (g4.read (n := 64) (r := 4) (by simp)).trans sp3
  have loaded4 := loaded_after call loaded3 sp3 wide4
  have grow4 := fun a h ↦ g4.grow a (grow3 a h)
  have same4 : stackPtr s4=stackPtr s0 := sp4.trans sp0.symm
  have total4 : AgreesExcept (components (stackPtr s0)) s0 s4 := by
    rw [same3] at wide4
    exact (total3.trans wide4).mono (by simp)
  obtain ⟨s5,a5,ready5,e5⟩ := (LegacyLoad.mov_r32_m32_legacy_effect_step 0x106a5c 0 (.sib 4 none 0 (.d32 171)) (by decide) rfl rfl).advances ready4
    (programText_slice (programLoaded_codeIn loaded4) 0x6a5c _ (by decide) (by decide +kernel))
    ⟨e4.rip,readable call grow4 sp4 (off := 171) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a63 (by decide)))
  have g5 : AgreesExcept [.reg 0,.rip] s4 s5 := e5.agrees
  have wide5 : AgreesExcept (components (stackPtr s4)) s4 s5 := g5.mono (by simp [components])
  have w5 : Window s5 f4 305 := window_registers w4 g5 (by simp) (by simp [Component.Covers])
  have v5 : s5.regValue .rax = (memLoad s4.external (stackPtr s4+171) 32).setWidth 64 := e5.writes
  have sp5 : stackPtr s5=stackPtr initial-504 := (g5.read (n := 64) (r := 4) (by simp)).trans sp4
  have loaded5 := loaded_after call loaded4 sp4 wide5
  have grow5 := fun a h ↦ g5.grow a (grow4 a h)
  have same5 : stackPtr s5=stackPtr s0 := sp5.trans sp0.symm
  have total5 : AgreesExcept (components (stackPtr s0)) s0 s5 := by
    rw [same4] at wide5
    exact (total4.trans wide5).mono (by simp)
  obtain ⟨s6,a6,ready6,e6⟩ := (LegacyLoad.mov_r32_m32_legacy_effect_step 0x106a63 1 (.sib 4 none 0 (.d32 175)) (by decide) rfl rfl).advances ready5
    (programText_slice (programLoaded_codeIn loaded5) 0x6a63 _ (by decide) (by decide +kernel))
    ⟨e5.rip,readable call grow5 sp5 (off := 175) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a6a (by decide)))
  have g6 : AgreesExcept [.reg 1,.rip] s5 s6 := e6.agrees
  have wide6 : AgreesExcept (components (stackPtr s5)) s5 s6 := g6.mono (by simp [components])
  have w6 : Window s6 f4 305 := window_registers w5 g6 (by simp) (by simp [Component.Covers])
  have v6 : s6.regValue .rcx = (memLoad s5.external (stackPtr s5+175) 32).setWidth 64 := e6.writes
  have sp6 : stackPtr s6=stackPtr initial-504 := (g6.read (n := 64) (r := 4) (by simp)).trans sp5
  have loaded6 := loaded_after call loaded5 sp5 wide6
  have grow6 := fun a h ↦ g6.grow a (grow5 a h)
  have same6 : stackPtr s6=stackPtr s0 := sp6.trans sp0.symm
  have total6 : AgreesExcept (components (stackPtr s0)) s0 s6 := by
    rw [same5] at wide6
    exact (total5.trans wide6).mono (by simp)
  obtain ⟨s7,a7,ready7,e7⟩ := (mov_r64_m64_effect_step 0x106a6a 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 179)) (by decide) rfl rfl).advances ready6
    (programText_slice (programLoaded_codeIn loaded6) 0x6a6a _ (by decide) (by decide +kernel))
    ⟨e6.rip,readable call grow6 sp6 (off := 179) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a72 (by decide)))
  have g7 : AgreesExcept [.reg 2,.rip] s6 s7 := e7.agrees
  have wide7 : AgreesExcept (components (stackPtr s6)) s6 s7 := g7.mono (by simp [components])
  have w7 : Window s7 f4 305 := window_registers w6 g7 (by simp) (by simp [Component.Covers])
  have v7 : s7.regValue .rdx = (memLoad s6.external (stackPtr s6+179) 64) := e7.writes
  have sp7 : stackPtr s7=stackPtr initial-504 := (g7.read (n := 64) (r := 4) (by simp)).trans sp6
  have loaded7 := loaded_after call loaded6 sp6 wide7
  have grow7 := fun a h ↦ g7.grow a (grow6 a h)
  have same7 : stackPtr s7=stackPtr s0 := sp7.trans sp0.symm
  have total7 : AgreesExcept (components (stackPtr s0)) s0 s7 := by
    rw [same6] at wide7
    exact (total6.trans wide7).mono (by simp)
  obtain ⟨s8,a8,ready8,e8⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106a72 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl).advances ready7
    (programText_slice (programLoaded_codeIn loaded7) 0x6a72 _ (by decide) (by decide +kernel))
    ⟨e7.rip,writable call grow7 sp7 (off := 48) (by decide) (by decide),code_apart call sp7 (off := 48) (len := 8) (pc := 0x6a72) (n := 5) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a77 (by decide)))
  have g8 : AgreesExcept [.mem (stackPtr s7+48) 8,.rip] s7 s8 := by
    have h := e8.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide8 := store_agrees g8 (by decide)
  have value8 : memLoad s8.external (stackPtr s7+48) 64 =
      memLoad s6.external (stackPtr s6+179) 64 := by
    have h : memLoad s8.external (stackPtr s7+48) 64 = (s7.regValue .rdx) := e8.writes
    have reg : s7.regValue .rdx = (memLoad s6.external (stackPtr s6+179) 64) := v7
    rw [h,reg]
  let f8 := update f4 (fun j ↦ f4 (179+j)) 48 8
  have w8 : Window s8 f8 305 := window_store_bounded (by decide) w7 w6
    (by decide) (by decide) g8 value8
  have sp8 : stackPtr s8=stackPtr initial-504 := (g8.read (n := 64) (r := 4) (by simp)).trans sp7
  have loaded8 := loaded_after call loaded7 sp7 wide8
  have grow8 := fun a h ↦ g8.grow a (grow7 a h)
  have same8 : stackPtr s8=stackPtr s0 := sp8.trans sp0.symm
  have total8 : AgreesExcept (components (stackPtr s0)) s0 s8 := by
    rw [same7] at wide8
    exact (total7.trans wide8).mono (by simp)
  obtain ⟨s9,a9,ready9,e9⟩ := (mov_r64_m64_effect_step 0x106a77 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 187)) (by decide) rfl rfl).advances ready8
    (programText_slice (programLoaded_codeIn loaded8) 0x6a77 _ (by decide) (by decide +kernel))
    ⟨e8.rip,readable call grow8 sp8 (off := 187) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a7f (by decide)))
  have g9 : AgreesExcept [.reg 2,.rip] s8 s9 := e9.agrees
  have wide9 : AgreesExcept (components (stackPtr s8)) s8 s9 := g9.mono (by simp [components])
  have w9 : Window s9 f8 305 := window_registers w8 g9 (by simp) (by simp [Component.Covers])
  have v9 : s9.regValue .rdx = (memLoad s8.external (stackPtr s8+187) 64) := e9.writes
  have sp9 : stackPtr s9=stackPtr initial-504 := (g9.read (n := 64) (r := 4) (by simp)).trans sp8
  have loaded9 := loaded_after call loaded8 sp8 wide9
  have grow9 := fun a h ↦ g9.grow a (grow8 a h)
  have same9 : stackPtr s9=stackPtr s0 := sp9.trans sp0.symm
  have total9 : AgreesExcept (components (stackPtr s0)) s0 s9 := by
    rw [same8] at wide9
    exact (total8.trans wide9).mono (by simp)
  obtain ⟨s10,a10,ready10,e10⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106a7f 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl).advances ready9
    (programText_slice (programLoaded_codeIn loaded9) 0x6a7f _ (by decide) (by decide +kernel))
    ⟨e9.rip,writable call grow9 sp9 (off := 56) (by decide) (by decide),code_apart call sp9 (off := 56) (len := 8) (pc := 0x6a7f) (n := 5) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a84 (by decide)))
  have g10 : AgreesExcept [.mem (stackPtr s9+56) 8,.rip] s9 s10 := by
    have h := e10.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide10 := store_agrees g10 (by decide)
  have value10 : memLoad s10.external (stackPtr s9+56) 64 =
      memLoad s8.external (stackPtr s8+187) 64 := by
    have h : memLoad s10.external (stackPtr s9+56) 64 = (s9.regValue .rdx) := e10.writes
    have reg : s9.regValue .rdx = (memLoad s8.external (stackPtr s8+187) 64) := v9
    rw [h,reg]
  let f10 := update f8 (fun j ↦ f8 (187+j)) 56 8
  have w10 : Window s10 f10 305 := window_store_bounded (by decide) w9 w8
    (by decide) (by decide) g10 value10
  have sp10 : stackPtr s10=stackPtr initial-504 := (g10.read (n := 64) (r := 4) (by simp)).trans sp9
  have loaded10 := loaded_after call loaded9 sp9 wide10
  have grow10 := fun a h ↦ g10.grow a (grow9 a h)
  have same10 : stackPtr s10=stackPtr s0 := sp10.trans sp0.symm
  have total10 : AgreesExcept (components (stackPtr s0)) s0 s10 := by
    rw [same9] at wide10
    exact (total9.trans wide10).mono (by simp)
  obtain ⟨s11,a11,ready11,e11⟩ := (mov_r64_m64_effect_step 0x106a84 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 195)) (by decide) rfl rfl).advances ready10
    (programText_slice (programLoaded_codeIn loaded10) 0x6a84 _ (by decide) (by decide +kernel))
    ⟨e10.rip,readable call grow10 sp10 (off := 195) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a8c (by decide)))
  have g11 : AgreesExcept [.reg 2,.rip] s10 s11 := e11.agrees
  have wide11 : AgreesExcept (components (stackPtr s10)) s10 s11 := g11.mono (by simp [components])
  have w11 : Window s11 f10 305 := window_registers w10 g11 (by simp) (by simp [Component.Covers])
  have v11 : s11.regValue .rdx = (memLoad s10.external (stackPtr s10+195) 64) := e11.writes
  have sp11 : stackPtr s11=stackPtr initial-504 := (g11.read (n := 64) (r := 4) (by simp)).trans sp10
  have loaded11 := loaded_after call loaded10 sp10 wide11
  have grow11 := fun a h ↦ g11.grow a (grow10 a h)
  have same11 : stackPtr s11=stackPtr s0 := sp11.trans sp0.symm
  have total11 : AgreesExcept (components (stackPtr s0)) s0 s11 := by
    rw [same10] at wide11
    exact (total10.trans wide11).mono (by simp)
  obtain ⟨s12,a12,ready12,e12⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106a8c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl).advances ready11
    (programText_slice (programLoaded_codeIn loaded11) 0x6a8c _ (by decide) (by decide +kernel))
    ⟨e11.rip,writable call grow11 sp11 (off := 64) (by decide) (by decide),code_apart call sp11 (off := 64) (len := 8) (pc := 0x6a8c) (n := 5) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a91 (by decide)))
  have g12 : AgreesExcept [.mem (stackPtr s11+64) 8,.rip] s11 s12 := by
    have h := e12.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide12 := store_agrees g12 (by decide)
  have value12 : memLoad s12.external (stackPtr s11+64) 64 =
      memLoad s10.external (stackPtr s10+195) 64 := by
    have h : memLoad s12.external (stackPtr s11+64) 64 = (s11.regValue .rdx) := e12.writes
    have reg : s11.regValue .rdx = (memLoad s10.external (stackPtr s10+195) 64) := v11
    rw [h,reg]
  let f12 := update f10 (fun j ↦ f10 (195+j)) 64 8
  have w12 : Window s12 f12 305 := window_store_bounded (by decide) w11 w10
    (by decide) (by decide) g12 value12
  have sp12 : stackPtr s12=stackPtr initial-504 := (g12.read (n := 64) (r := 4) (by simp)).trans sp11
  have loaded12 := loaded_after call loaded11 sp11 wide12
  have grow12 := fun a h ↦ g12.grow a (grow11 a h)
  have same12 : stackPtr s12=stackPtr s0 := sp12.trans sp0.symm
  have total12 : AgreesExcept (components (stackPtr s0)) s0 s12 := by
    rw [same11] at wide12
    exact (total11.trans wide12).mono (by simp)
  obtain ⟨s13,a13,ready13,e13⟩ := (mov_r64_m64_effect_step 0x106a91 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 203)) (by decide) rfl rfl).advances ready12
    (programText_slice (programLoaded_codeIn loaded12) 0x6a91 _ (by decide) (by decide +kernel))
    ⟨e12.rip,readable call grow12 sp12 (off := 203) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a99 (by decide)))
  have g13 : AgreesExcept [.reg 2,.rip] s12 s13 := e13.agrees
  have wide13 : AgreesExcept (components (stackPtr s12)) s12 s13 := g13.mono (by simp [components])
  have w13 : Window s13 f12 305 := window_registers w12 g13 (by simp) (by simp [Component.Covers])
  have v13 : s13.regValue .rdx = (memLoad s12.external (stackPtr s12+203) 64) := e13.writes
  have sp13 : stackPtr s13=stackPtr initial-504 := (g13.read (n := 64) (r := 4) (by simp)).trans sp12
  have loaded13 := loaded_after call loaded12 sp12 wide13
  have grow13 := fun a h ↦ g13.grow a (grow12 a h)
  have same13 : stackPtr s13=stackPtr s0 := sp13.trans sp0.symm
  have total13 : AgreesExcept (components (stackPtr s0)) s0 s13 := by
    rw [same12] at wide13
    exact (total12.trans wide13).mono (by simp)
  obtain ⟨s14,a14,ready14,e14⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106a99 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl).advances ready13
    (programText_slice (programLoaded_codeIn loaded13) 0x6a99 _ (by decide) (by decide +kernel))
    ⟨e13.rip,writable call grow13 sp13 (off := 72) (by decide) (by decide),code_apart call sp13 (off := 72) (len := 8) (pc := 0x6a99) (n := 5) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6a9e (by decide)))
  have g14 : AgreesExcept [.mem (stackPtr s13+72) 8,.rip] s13 s14 := by
    have h := e14.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide14 := store_agrees g14 (by decide)
  have value14 : memLoad s14.external (stackPtr s13+72) 64 =
      memLoad s12.external (stackPtr s12+203) 64 := by
    have h : memLoad s14.external (stackPtr s13+72) 64 = (s13.regValue .rdx) := e14.writes
    have reg : s13.regValue .rdx = (memLoad s12.external (stackPtr s12+203) 64) := v13
    rw [h,reg]
  let f14 := update f12 (fun j ↦ f12 (203+j)) 72 8
  have w14 : Window s14 f14 305 := window_store_bounded (by decide) w13 w12
    (by decide) (by decide) g14 value14
  have sp14 : stackPtr s14=stackPtr initial-504 := (g14.read (n := 64) (r := 4) (by simp)).trans sp13
  have loaded14 := loaded_after call loaded13 sp13 wide14
  have grow14 := fun a h ↦ g14.grow a (grow13 a h)
  have same14 : stackPtr s14=stackPtr s0 := sp14.trans sp0.symm
  have total14 : AgreesExcept (components (stackPtr s0)) s0 s14 := by
    rw [same13] at wide14
    exact (total13.trans wide14).mono (by simp)
  obtain ⟨s15,a15,ready15,e15⟩ := (mov_r64_m64_effect_step 0x106a9e 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 211)) (by decide) rfl rfl).advances ready14
    (programText_slice (programLoaded_codeIn loaded14) 0x6a9e _ (by decide) (by decide +kernel))
    ⟨e14.rip,readable call grow14 sp14 (off := 211) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6aa6 (by decide)))
  have g15 : AgreesExcept [.reg 2,.rip] s14 s15 := e15.agrees
  have wide15 : AgreesExcept (components (stackPtr s14)) s14 s15 := g15.mono (by simp [components])
  have w15 : Window s15 f14 305 := window_registers w14 g15 (by simp) (by simp [Component.Covers])
  have v15 : s15.regValue .rdx = (memLoad s14.external (stackPtr s14+211) 64) := e15.writes
  have sp15 : stackPtr s15=stackPtr initial-504 := (g15.read (n := 64) (r := 4) (by simp)).trans sp14
  have loaded15 := loaded_after call loaded14 sp14 wide15
  have grow15 := fun a h ↦ g15.grow a (grow14 a h)
  have same15 : stackPtr s15=stackPtr s0 := sp15.trans sp0.symm
  have total15 : AgreesExcept (components (stackPtr s0)) s0 s15 := by
    rw [same14] at wide15
    exact (total14.trans wide15).mono (by simp)
  obtain ⟨s16,a16,ready16,e16⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106aa6 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl).advances ready15
    (programText_slice (programLoaded_codeIn loaded15) 0x6aa6 _ (by decide) (by decide +kernel))
    ⟨e15.rip,writable call grow15 sp15 (off := 80) (by decide) (by decide),code_apart call sp15 (off := 80) (len := 8) (pc := 0x6aa6) (n := 5) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6aab (by decide)))
  have g16 : AgreesExcept [.mem (stackPtr s15+80) 8,.rip] s15 s16 := by
    have h := e16.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide16 := store_agrees g16 (by decide)
  have value16 : memLoad s16.external (stackPtr s15+80) 64 =
      memLoad s14.external (stackPtr s14+211) 64 := by
    have h : memLoad s16.external (stackPtr s15+80) 64 = (s15.regValue .rdx) := e16.writes
    have reg : s15.regValue .rdx = (memLoad s14.external (stackPtr s14+211) 64) := v15
    rw [h,reg]
  let f16 := update f14 (fun j ↦ f14 (211+j)) 80 8
  have w16 : Window s16 f16 305 := window_store_bounded (by decide) w15 w14
    (by decide) (by decide) g16 value16
  have sp16 : stackPtr s16=stackPtr initial-504 := (g16.read (n := 64) (r := 4) (by simp)).trans sp15
  have loaded16 := loaded_after call loaded15 sp15 wide16
  have grow16 := fun a h ↦ g16.grow a (grow15 a h)
  have same16 : stackPtr s16=stackPtr s0 := sp16.trans sp0.symm
  have total16 : AgreesExcept (components (stackPtr s0)) s0 s16 := by
    rw [same15] at wide16
    exact (total15.trans wide16).mono (by simp)
  obtain ⟨s17,a17,ready17,e17⟩ := (mov_r64_m64_effect_step 0x106aab 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 219)) (by decide) rfl rfl).advances ready16
    (programText_slice (programLoaded_codeIn loaded16) 0x6aab _ (by decide) (by decide +kernel))
    ⟨e16.rip,readable call grow16 sp16 (off := 219) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ab3 (by decide)))
  have g17 : AgreesExcept [.reg 2,.rip] s16 s17 := e17.agrees
  have wide17 : AgreesExcept (components (stackPtr s16)) s16 s17 := g17.mono (by simp [components])
  have w17 : Window s17 f16 305 := window_registers w16 g17 (by simp) (by simp [Component.Covers])
  have v17 : s17.regValue .rdx = (memLoad s16.external (stackPtr s16+219) 64) := e17.writes
  have sp17 : stackPtr s17=stackPtr initial-504 := (g17.read (n := 64) (r := 4) (by simp)).trans sp16
  have loaded17 := loaded_after call loaded16 sp16 wide17
  have grow17 := fun a h ↦ g17.grow a (grow16 a h)
  have same17 : stackPtr s17=stackPtr s0 := sp17.trans sp0.symm
  have total17 : AgreesExcept (components (stackPtr s0)) s0 s17 := by
    rw [same16] at wide17
    exact (total16.trans wide17).mono (by simp)
  obtain ⟨s18,a18,ready18,e18⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106ab3 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl).advances ready17
    (programText_slice (programLoaded_codeIn loaded17) 0x6ab3 _ (by decide) (by decide +kernel))
    ⟨e17.rip,writable call grow17 sp17 (off := 88) (by decide) (by decide),code_apart call sp17 (off := 88) (len := 8) (pc := 0x6ab3) (n := 5) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ab8 (by decide)))
  have g18 : AgreesExcept [.mem (stackPtr s17+88) 8,.rip] s17 s18 := by
    have h := e18.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide18 := store_agrees g18 (by decide)
  have value18 : memLoad s18.external (stackPtr s17+88) 64 =
      memLoad s16.external (stackPtr s16+219) 64 := by
    have h : memLoad s18.external (stackPtr s17+88) 64 = (s17.regValue .rdx) := e18.writes
    have reg : s17.regValue .rdx = (memLoad s16.external (stackPtr s16+219) 64) := v17
    rw [h,reg]
  let f18 := update f16 (fun j ↦ f16 (219+j)) 88 8
  have w18 : Window s18 f18 305 := window_store_bounded (by decide) w17 w16
    (by decide) (by decide) g18 value18
  have sp18 : stackPtr s18=stackPtr initial-504 := (g18.read (n := 64) (r := 4) (by simp)).trans sp17
  have loaded18 := loaded_after call loaded17 sp17 wide18
  have grow18 := fun a h ↦ g18.grow a (grow17 a h)
  have same18 : stackPtr s18=stackPtr s0 := sp18.trans sp0.symm
  have total18 : AgreesExcept (components (stackPtr s0)) s0 s18 := by
    rw [same17] at wide18
    exact (total17.trans wide18).mono (by simp)
  obtain ⟨s19,a19,ready19,e19⟩ := (mov_r64_m64_effect_step 0x106ab8 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 225)) (by decide) rfl rfl).advances ready18
    (programText_slice (programLoaded_codeIn loaded18) 0x6ab8 _ (by decide) (by decide +kernel))
    ⟨e18.rip,readable call grow18 sp18 (off := 225) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ac0 (by decide)))
  have g19 : AgreesExcept [.reg 2,.rip] s18 s19 := e19.agrees
  have wide19 : AgreesExcept (components (stackPtr s18)) s18 s19 := g19.mono (by simp [components])
  have w19 : Window s19 f18 305 := window_registers w18 g19 (by simp) (by simp [Component.Covers])
  have v19 : s19.regValue .rdx = (memLoad s18.external (stackPtr s18+225) 64) := e19.writes
  have sp19 : stackPtr s19=stackPtr initial-504 := (g19.read (n := 64) (r := 4) (by simp)).trans sp18
  have loaded19 := loaded_after call loaded18 sp18 wide19
  have grow19 := fun a h ↦ g19.grow a (grow18 a h)
  have same19 : stackPtr s19=stackPtr s0 := sp19.trans sp0.symm
  have total19 : AgreesExcept (components (stackPtr s0)) s0 s19 := by
    rw [same18] at wide19
    exact (total18.trans wide19).mono (by simp)
  obtain ⟨s20,a20,ready20,e20⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106ac0 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 94)) (by decide) rfl rfl).advances ready19
    (programText_slice (programLoaded_codeIn loaded19) 0x6ac0 _ (by decide) (by decide +kernel))
    ⟨e19.rip,writable call grow19 sp19 (off := 94) (by decide) (by decide),code_apart call sp19 (off := 94) (len := 8) (pc := 0x6ac0) (n := 5) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ac5 (by decide)))
  have g20 : AgreesExcept [.mem (stackPtr s19+94) 8,.rip] s19 s20 := by
    have h := e20.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide20 := store_agrees g20 (by decide)
  have value20 : memLoad s20.external (stackPtr s19+94) 64 =
      memLoad s18.external (stackPtr s18+225) 64 := by
    have h : memLoad s20.external (stackPtr s19+94) 64 = (s19.regValue .rdx) := e20.writes
    have reg : s19.regValue .rdx = (memLoad s18.external (stackPtr s18+225) 64) := v19
    rw [h,reg]
  let f20 := update f18 (fun j ↦ f18 (225+j)) 94 8
  have w20 : Window s20 f20 305 := window_store_bounded (by decide) w19 w18
    (by decide) (by decide) g20 value20
  have sp20 : stackPtr s20=stackPtr initial-504 := (g20.read (n := 64) (r := 4) (by simp)).trans sp19
  have loaded20 := loaded_after call loaded19 sp19 wide20
  have grow20 := fun a h ↦ g20.grow a (grow19 a h)
  have same20 : stackPtr s20=stackPtr s0 := sp20.trans sp0.symm
  have total20 : AgreesExcept (components (stackPtr s0)) s0 s20 := by
    rw [same19] at wide20
    exact (total19.trans wide20).mono (by simp)
  obtain ⟨s21,a21,ready21,e21⟩ := (mov_r64_m64_effect_step 0x106ac5 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 94)) (by decide) rfl rfl).advances ready20
    (programText_slice (programLoaded_codeIn loaded20) 0x6ac5 _ (by decide) (by decide +kernel))
    ⟨e20.rip,readable call grow20 sp20 (off := 94) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6aca (by decide)))
  have g21 : AgreesExcept [.reg 2,.rip] s20 s21 := e21.agrees
  have wide21 : AgreesExcept (components (stackPtr s20)) s20 s21 := g21.mono (by simp [components])
  have w21 : Window s21 f20 305 := window_registers w20 g21 (by simp) (by simp [Component.Covers])
  have v21 : s21.regValue .rdx = (memLoad s20.external (stackPtr s20+94) 64) := e21.writes
  have sp21 : stackPtr s21=stackPtr initial-504 := (g21.read (n := 64) (r := 4) (by simp)).trans sp20
  have loaded21 := loaded_after call loaded20 sp20 wide21
  have grow21 := fun a h ↦ g21.grow a (grow20 a h)
  have same21 : stackPtr s21=stackPtr s0 := sp21.trans sp0.symm
  have total21 : AgreesExcept (components (stackPtr s0)) s0 s21 := by
    rw [same20] at wide21
    exact (total20.trans wide21).mono (by simp)
  obtain ⟨s22,a22,ready22,e22⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106aca 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 158)) (by decide) rfl rfl).advances ready21
    (programText_slice (programLoaded_codeIn loaded21) 0x6aca _ (by decide) (by decide +kernel))
    ⟨e21.rip,writable call grow21 sp21 (off := 158) (by decide) (by decide),code_apart call sp21 (off := 158) (len := 8) (pc := 0x6aca) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ad2 (by decide)))
  have g22 : AgreesExcept [.mem (stackPtr s21+158) 8,.rip] s21 s22 := by
    have h := e22.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide22 := store_agrees g22 (by decide)
  have value22 : memLoad s22.external (stackPtr s21+158) 64 =
      memLoad s20.external (stackPtr s20+94) 64 := by
    have h : memLoad s22.external (stackPtr s21+158) 64 = (s21.regValue .rdx) := e22.writes
    have reg : s21.regValue .rdx = (memLoad s20.external (stackPtr s20+94) 64) := v21
    rw [h,reg]
  let f22 := update f20 (fun j ↦ f20 (94+j)) 158 8
  have w22 : Window s22 f22 305 := window_store_bounded (by decide) w21 w20
    (by decide) (by decide) g22 value22
  have sp22 : stackPtr s22=stackPtr initial-504 := (g22.read (n := 64) (r := 4) (by simp)).trans sp21
  have loaded22 := loaded_after call loaded21 sp21 wide22
  have grow22 := fun a h ↦ g22.grow a (grow21 a h)
  have same22 : stackPtr s22=stackPtr s0 := sp22.trans sp0.symm
  have total22 : AgreesExcept (components (stackPtr s0)) s0 s22 := by
    rw [same21] at wide22
    exact (total21.trans wide22).mono (by simp)
  obtain ⟨s23,a23,ready23,e23⟩ := (mov_r64_m64_effect_step 0x106ad2 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl).advances ready22
    (programText_slice (programLoaded_codeIn loaded22) 0x6ad2 _ (by decide) (by decide +kernel))
    ⟨e22.rip,readable call grow22 sp22 (off := 88) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ad7 (by decide)))
  have g23 : AgreesExcept [.reg 2,.rip] s22 s23 := e23.agrees
  have wide23 : AgreesExcept (components (stackPtr s22)) s22 s23 := g23.mono (by simp [components])
  have w23 : Window s23 f22 305 := window_registers w22 g23 (by simp) (by simp [Component.Covers])
  have v23 : s23.regValue .rdx = (memLoad s22.external (stackPtr s22+88) 64) := e23.writes
  have sp23 : stackPtr s23=stackPtr initial-504 := (g23.read (n := 64) (r := 4) (by simp)).trans sp22
  have loaded23 := loaded_after call loaded22 sp22 wide23
  have grow23 := fun a h ↦ g23.grow a (grow22 a h)
  have same23 : stackPtr s23=stackPtr s0 := sp23.trans sp0.symm
  have total23 : AgreesExcept (components (stackPtr s0)) s0 s23 := by
    rw [same22] at wide23
    exact (total22.trans wide23).mono (by simp)
  obtain ⟨s24,a24,ready24,e24⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106ad7 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl).advances ready23
    (programText_slice (programLoaded_codeIn loaded23) 0x6ad7 _ (by decide) (by decide +kernel))
    ⟨e23.rip,writable call grow23 sp23 (off := 152) (by decide) (by decide),code_apart call sp23 (off := 152) (len := 8) (pc := 0x6ad7) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6adf (by decide)))
  have g24 : AgreesExcept [.mem (stackPtr s23+152) 8,.rip] s23 s24 := by
    have h := e24.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide24 := store_agrees g24 (by decide)
  have value24 : memLoad s24.external (stackPtr s23+152) 64 =
      memLoad s22.external (stackPtr s22+88) 64 := by
    have h : memLoad s24.external (stackPtr s23+152) 64 = (s23.regValue .rdx) := e24.writes
    have reg : s23.regValue .rdx = (memLoad s22.external (stackPtr s22+88) 64) := v23
    rw [h,reg]
  let f24 := update f22 (fun j ↦ f22 (88+j)) 152 8
  have w24 : Window s24 f24 305 := window_store_bounded (by decide) w23 w22
    (by decide) (by decide) g24 value24
  have sp24 : stackPtr s24=stackPtr initial-504 := (g24.read (n := 64) (r := 4) (by simp)).trans sp23
  have loaded24 := loaded_after call loaded23 sp23 wide24
  have grow24 := fun a h ↦ g24.grow a (grow23 a h)
  have same24 : stackPtr s24=stackPtr s0 := sp24.trans sp0.symm
  have total24 : AgreesExcept (components (stackPtr s0)) s0 s24 := by
    rw [same23] at wide24
    exact (total23.trans wide24).mono (by simp)
  obtain ⟨s25,a25,ready25,e25⟩ := (mov_r64_m64_effect_step 0x106adf 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl).advances ready24
    (programText_slice (programLoaded_codeIn loaded24) 0x6adf _ (by decide) (by decide +kernel))
    ⟨e24.rip,readable call grow24 sp24 (off := 48) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ae4 (by decide)))
  have g25 : AgreesExcept [.reg 2,.rip] s24 s25 := e25.agrees
  have wide25 : AgreesExcept (components (stackPtr s24)) s24 s25 := g25.mono (by simp [components])
  have w25 : Window s25 f24 305 := window_registers w24 g25 (by simp) (by simp [Component.Covers])
  have v25 : s25.regValue .rdx = (memLoad s24.external (stackPtr s24+48) 64) := e25.writes
  have sp25 : stackPtr s25=stackPtr initial-504 := (g25.read (n := 64) (r := 4) (by simp)).trans sp24
  have loaded25 := loaded_after call loaded24 sp24 wide25
  have grow25 := fun a h ↦ g25.grow a (grow24 a h)
  have same25 : stackPtr s25=stackPtr s0 := sp25.trans sp0.symm
  have total25 : AgreesExcept (components (stackPtr s0)) s0 s25 := by
    rw [same24] at wide25
    exact (total24.trans wide25).mono (by simp)
  obtain ⟨s26,a26,ready26,e26⟩ := (mov_r64_m64_effect_step 0x106ae4 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl).advances ready25
    (programText_slice (programLoaded_codeIn loaded25) 0x6ae4 _ (by decide) (by decide +kernel))
    ⟨e25.rip,readable call grow25 sp25 (off := 56) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ae9 (by decide)))
  have g26 : AgreesExcept [.reg 6,.rip] s25 s26 := e26.agrees
  have wide26 : AgreesExcept (components (stackPtr s25)) s25 s26 := g26.mono (by simp [components])
  have w26 : Window s26 f24 305 := window_registers w25 g26 (by simp) (by simp [Component.Covers])
  have v26 : s26.regValue .rsi = (memLoad s25.external (stackPtr s25+56) 64) := e26.writes
  have sp26 : stackPtr s26=stackPtr initial-504 := (g26.read (n := 64) (r := 4) (by simp)).trans sp25
  have loaded26 := loaded_after call loaded25 sp25 wide26
  have grow26 := fun a h ↦ g26.grow a (grow25 a h)
  have same26 : stackPtr s26=stackPtr s0 := sp26.trans sp0.symm
  have total26 : AgreesExcept (components (stackPtr s0)) s0 s26 := by
    rw [same25] at wide26
    exact (total25.trans wide26).mono (by simp)
  obtain ⟨s27,a27,ready27,e27⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106ae9 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl).advances ready26
    (programText_slice (programLoaded_codeIn loaded26) 0x6ae9 _ (by decide) (by decide +kernel))
    ⟨e26.rip,writable call grow26 sp26 (off := 112) (by decide) (by decide),code_apart call sp26 (off := 112) (len := 8) (pc := 0x6ae9) (n := 5) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6aee (by decide)))
  have g27 : AgreesExcept [.mem (stackPtr s26+112) 8,.rip] s26 s27 := by
    have h := e27.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide27 := store_agrees g27 (by decide)
  have value27 : memLoad s27.external (stackPtr s26+112) 64 =
      memLoad s24.external (stackPtr s24+48) 64 := by
    have h : memLoad s27.external (stackPtr s26+112) 64 = (s26.regValue .rdx) := e27.writes
    have reg : s26.regValue .rdx = (memLoad s24.external (stackPtr s24+48) 64) := (g26.read (n := 64) (r := 2) (by simp)).trans v25
    rw [h,reg]
  let f27 := update f24 (fun j ↦ f24 (48+j)) 112 8
  have w27 : Window s27 f27 305 := window_store_bounded (by decide) w26 w24
    (by decide) (by decide) g27 value27
  have sp27 : stackPtr s27=stackPtr initial-504 := (g27.read (n := 64) (r := 4) (by simp)).trans sp26
  have loaded27 := loaded_after call loaded26 sp26 wide27
  have grow27 := fun a h ↦ g27.grow a (grow26 a h)
  have same27 : stackPtr s27=stackPtr s0 := sp27.trans sp0.symm
  have total27 : AgreesExcept (components (stackPtr s0)) s0 s27 := by
    rw [same26] at wide27
    exact (total26.trans wide27).mono (by simp)
  obtain ⟨s28,a28,ready28,e28⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106aee 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl).advances ready27
    (programText_slice (programLoaded_codeIn loaded27) 0x6aee _ (by decide) (by decide +kernel))
    ⟨e27.rip,writable call grow27 sp27 (off := 120) (by decide) (by decide),code_apart call sp27 (off := 120) (len := 8) (pc := 0x6aee) (n := 5) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6af3 (by decide)))
  have g28 : AgreesExcept [.mem (stackPtr s27+120) 8,.rip] s27 s28 := by
    have h := e28.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide28 := store_agrees g28 (by decide)
  have value28 : memLoad s28.external (stackPtr s27+120) 64 =
      memLoad s25.external (stackPtr s25+56) 64 := by
    have h : memLoad s28.external (stackPtr s27+120) 64 = (s27.regValue .rsi) := e28.writes
    have reg : s27.regValue .rsi = (memLoad s25.external (stackPtr s25+56) 64) := (g27.read (n := 64) (r := 6) (by simp)).trans v26
    rw [h,reg]
  let f28 := update f27 (fun j ↦ f24 (56+j)) 120 8
  have w28 : Window s28 f28 305 := window_store_bounded (by decide) w27 w25
    (by decide) (by decide) g28 value28
  have sp28 : stackPtr s28=stackPtr initial-504 := (g28.read (n := 64) (r := 4) (by simp)).trans sp27
  have loaded28 := loaded_after call loaded27 sp27 wide28
  have grow28 := fun a h ↦ g28.grow a (grow27 a h)
  have same28 : stackPtr s28=stackPtr s0 := sp28.trans sp0.symm
  have total28 : AgreesExcept (components (stackPtr s0)) s0 s28 := by
    rw [same27] at wide28
    exact (total27.trans wide28).mono (by simp)
  obtain ⟨s29,a29,ready29,e29⟩ := (mov_r64_m64_effect_step 0x106af3 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl).advances ready28
    (programText_slice (programLoaded_codeIn loaded28) 0x6af3 _ (by decide) (by decide +kernel))
    ⟨e28.rip,readable call grow28 sp28 (off := 64) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6af8 (by decide)))
  have g29 : AgreesExcept [.reg 7,.rip] s28 s29 := e29.agrees
  have wide29 : AgreesExcept (components (stackPtr s28)) s28 s29 := g29.mono (by simp [components])
  have w29 : Window s29 f28 305 := window_registers w28 g29 (by simp) (by simp [Component.Covers])
  have v29 : s29.regValue .rdi = (memLoad s28.external (stackPtr s28+64) 64) := e29.writes
  have sp29 : stackPtr s29=stackPtr initial-504 := (g29.read (n := 64) (r := 4) (by simp)).trans sp28
  have loaded29 := loaded_after call loaded28 sp28 wide29
  have grow29 := fun a h ↦ g29.grow a (grow28 a h)
  have same29 : stackPtr s29=stackPtr s0 := sp29.trans sp0.symm
  have total29 : AgreesExcept (components (stackPtr s0)) s0 s29 := by
    rw [same28] at wide29
    exact (total28.trans wide29).mono (by simp)
  obtain ⟨s30,a30,ready30,e30⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106af8 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl).advances ready29
    (programText_slice (programLoaded_codeIn loaded29) 0x6af8 _ (by decide) (by decide +kernel))
    ⟨e29.rip,writable call grow29 sp29 (off := 128) (by decide) (by decide),code_apart call sp29 (off := 128) (len := 8) (pc := 0x6af8) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b00 (by decide)))
  have g30 : AgreesExcept [.mem (stackPtr s29+128) 8,.rip] s29 s30 := by
    have h := e30.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide30 := store_agrees g30 (by decide)
  have value30 : memLoad s30.external (stackPtr s29+128) 64 =
      memLoad s28.external (stackPtr s28+64) 64 := by
    have h : memLoad s30.external (stackPtr s29+128) 64 = (s29.regValue .rdi) := e30.writes
    have reg : s29.regValue .rdi = (memLoad s28.external (stackPtr s28+64) 64) := v29
    rw [h,reg]
  let f30 := update f28 (fun j ↦ f28 (64+j)) 128 8
  have w30 : Window s30 f30 305 := window_store_bounded (by decide) w29 w28
    (by decide) (by decide) g30 value30
  have sp30 : stackPtr s30=stackPtr initial-504 := (g30.read (n := 64) (r := 4) (by simp)).trans sp29
  have loaded30 := loaded_after call loaded29 sp29 wide30
  have grow30 := fun a h ↦ g30.grow a (grow29 a h)
  have same30 : stackPtr s30=stackPtr s0 := sp30.trans sp0.symm
  have total30 : AgreesExcept (components (stackPtr s0)) s0 s30 := by
    rw [same29] at wide30
    exact (total29.trans wide30).mono (by simp)
  obtain ⟨s31,a31,ready31,e31⟩ := (mov_r64_m64_effect_step 0x106b00 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl).advances ready30
    (programText_slice (programLoaded_codeIn loaded30) 0x6b00 _ (by decide) (by decide +kernel))
    ⟨e30.rip,readable call grow30 sp30 (off := 72) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b05 (by decide)))
  have g31 : AgreesExcept [.reg 8,.rip] s30 s31 := e31.agrees
  have wide31 : AgreesExcept (components (stackPtr s30)) s30 s31 := g31.mono (by simp [components])
  have w31 : Window s31 f30 305 := window_registers w30 g31 (by simp) (by simp [Component.Covers])
  have v31 : s31.regValue .r8 = (memLoad s30.external (stackPtr s30+72) 64) := e31.writes
  have sp31 : stackPtr s31=stackPtr initial-504 := (g31.read (n := 64) (r := 4) (by simp)).trans sp30
  have loaded31 := loaded_after call loaded30 sp30 wide31
  have grow31 := fun a h ↦ g31.grow a (grow30 a h)
  have same31 : stackPtr s31=stackPtr s0 := sp31.trans sp0.symm
  have total31 : AgreesExcept (components (stackPtr s0)) s0 s31 := by
    rw [same30] at wide31
    exact (total30.trans wide31).mono (by simp)
  obtain ⟨s32,a32,ready32,e32⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106b05 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl).advances ready31
    (programText_slice (programLoaded_codeIn loaded31) 0x6b05 _ (by decide) (by decide +kernel))
    ⟨e31.rip,writable call grow31 sp31 (off := 136) (by decide) (by decide),code_apart call sp31 (off := 136) (len := 8) (pc := 0x6b05) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b0d (by decide)))
  have g32 : AgreesExcept [.mem (stackPtr s31+136) 8,.rip] s31 s32 := by
    have h := e32.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide32 := store_agrees g32 (by decide)
  have value32 : memLoad s32.external (stackPtr s31+136) 64 =
      memLoad s30.external (stackPtr s30+72) 64 := by
    have h : memLoad s32.external (stackPtr s31+136) 64 = (s31.regValue .r8) := e32.writes
    have reg : s31.regValue .r8 = (memLoad s30.external (stackPtr s30+72) 64) := v31
    rw [h,reg]
  let f32 := update f30 (fun j ↦ f30 (72+j)) 136 8
  have w32 : Window s32 f32 305 := window_store_bounded (by decide) w31 w30
    (by decide) (by decide) g32 value32
  have sp32 : stackPtr s32=stackPtr initial-504 := (g32.read (n := 64) (r := 4) (by simp)).trans sp31
  have loaded32 := loaded_after call loaded31 sp31 wide32
  have grow32 := fun a h ↦ g32.grow a (grow31 a h)
  have same32 : stackPtr s32=stackPtr s0 := sp32.trans sp0.symm
  have total32 : AgreesExcept (components (stackPtr s0)) s0 s32 := by
    rw [same31] at wide32
    exact (total31.trans wide32).mono (by simp)
  obtain ⟨s33,a33,ready33,e33⟩ := (mov_r64_m64_effect_step 0x106b0d 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl).advances ready32
    (programText_slice (programLoaded_codeIn loaded32) 0x6b0d _ (by decide) (by decide +kernel))
    ⟨e32.rip,readable call grow32 sp32 (off := 80) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b12 (by decide)))
  have g33 : AgreesExcept [.reg 9,.rip] s32 s33 := e33.agrees
  have wide33 : AgreesExcept (components (stackPtr s32)) s32 s33 := g33.mono (by simp [components])
  have w33 : Window s33 f32 305 := window_registers w32 g33 (by simp) (by simp [Component.Covers])
  have v33 : s33.regValue .r9 = (memLoad s32.external (stackPtr s32+80) 64) := e33.writes
  have sp33 : stackPtr s33=stackPtr initial-504 := (g33.read (n := 64) (r := 4) (by simp)).trans sp32
  have loaded33 := loaded_after call loaded32 sp32 wide33
  have grow33 := fun a h ↦ g33.grow a (grow32 a h)
  have same33 : stackPtr s33=stackPtr s0 := sp33.trans sp0.symm
  have total33 : AgreesExcept (components (stackPtr s0)) s0 s33 := by
    rw [same32] at wide33
    exact (total32.trans wide33).mono (by simp)
  obtain ⟨s34,a34,ready34,e34⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106b12 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl).advances ready33
    (programText_slice (programLoaded_codeIn loaded33) 0x6b12 _ (by decide) (by decide +kernel))
    ⟨e33.rip,writable call grow33 sp33 (off := 144) (by decide) (by decide),code_apart call sp33 (off := 144) (len := 8) (pc := 0x6b12) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b1a (by decide)))
  have g34 : AgreesExcept [.mem (stackPtr s33+144) 8,.rip] s33 s34 := by
    have h := e34.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide34 := store_agrees g34 (by decide)
  have value34 : memLoad s34.external (stackPtr s33+144) 64 =
      memLoad s32.external (stackPtr s32+80) 64 := by
    have h : memLoad s34.external (stackPtr s33+144) 64 = (s33.regValue .r9) := e34.writes
    have reg : s33.regValue .r9 = (memLoad s32.external (stackPtr s32+80) 64) := v33
    rw [h,reg]
  let f34 := update f32 (fun j ↦ f32 (80+j)) 144 8
  have w34 : Window s34 f34 305 := window_store_bounded (by decide) w33 w32
    (by decide) (by decide) g34 value34
  have sp34 : stackPtr s34=stackPtr initial-504 := (g34.read (n := 64) (r := 4) (by simp)).trans sp33
  have loaded34 := loaded_after call loaded33 sp33 wide34
  have grow34 := fun a h ↦ g34.grow a (grow33 a h)
  have same34 : stackPtr s34=stackPtr s0 := sp34.trans sp0.symm
  have total34 : AgreesExcept (components (stackPtr s0)) s0 s34 := by
    rw [same33] at wide34
    exact (total33.trans wide34).mono (by simp)
  obtain ⟨s35,a35,ready35,e35⟩ := (CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x106b1a 1 (.sib 4 none 0 (.d32 247)) (by decide) rfl rfl).advances ready34
    (programText_slice (programLoaded_codeIn loaded34) 0x6b1a _ (by decide) (by decide +kernel))
    ⟨e34.rip,writable call grow34 sp34 (off := 247) (by decide) (by decide),code_apart call sp34 (off := 247) (len := 4) (pc := 0x6b1a) (n := 7) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b21 (by decide)))
  have g35 : AgreesExcept [.mem (stackPtr s34+247) 4,.rip] s34 s35 := by
    have h := e35.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide35 := store_agrees g35 (by decide)
  have value35 : memLoad s35.external (stackPtr s34+247) 32 =
      memLoad s5.external (stackPtr s5+175) 32 := by
    have h : memLoad s35.external (stackPtr s34+247) 32 = (s34.regValue .rcx).setWidth 32 := e35.writes
    have reg : s34.regValue .rcx = (memLoad s5.external (stackPtr s5+175) 32).setWidth 64 := ((((((((((((((((((((((((((((g7.trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).trans g20).trans g21).trans g22).trans g23).trans g24).trans g25).trans g26).trans g27).trans g28).trans g29).trans g30).trans g31).trans g32).trans g33).trans g34).read (n := 64) (r := 1) (by simp)).trans v6
    rw [h,reg]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),BitVec.setWidth_eq]
  let f35 := update f34 (fun j ↦ f4 (175+j)) 247 4
  have w35 : Window s35 f35 305 := window_store_bounded (by decide) w34 w5
    (by decide) (by decide) g35 value35
  have sp35 : stackPtr s35=stackPtr initial-504 := (g35.read (n := 64) (r := 4) (by simp)).trans sp34
  have loaded35 := loaded_after call loaded34 sp34 wide35
  have grow35 := fun a h ↦ g35.grow a (grow34 a h)
  have same35 : stackPtr s35=stackPtr s0 := sp35.trans sp0.symm
  have total35 : AgreesExcept (components (stackPtr s0)) s0 s35 := by
    rw [same34] at wide35
    exact (total34.trans wide35).mono (by simp)
  obtain ⟨s36,a36,ready36,e36⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106b21 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 251)) (by decide) rfl rfl).advances ready35
    (programText_slice (programLoaded_codeIn loaded35) 0x6b21 _ (by decide) (by decide +kernel))
    ⟨e35.rip,writable call grow35 sp35 (off := 251) (by decide) (by decide),code_apart call sp35 (off := 251) (len := 8) (pc := 0x6b21) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b29 (by decide)))
  have g36 : AgreesExcept [.mem (stackPtr s35+251) 8,.rip] s35 s36 := by
    have h := e36.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide36 := store_agrees g36 (by decide)
  have value36 : memLoad s36.external (stackPtr s35+251) 64 =
      memLoad s24.external (stackPtr s24+48) 64 := by
    have h : memLoad s36.external (stackPtr s35+251) 64 = (s35.regValue .rdx) := e36.writes
    have reg : s35.regValue .rdx = (memLoad s24.external (stackPtr s24+48) 64) := ((((((((((g26.trans g27).trans g28).trans g29).trans g30).trans g31).trans g32).trans g33).trans g34).trans g35).read (n := 64) (r := 2) (by simp)).trans v25
    rw [h,reg]
  let f36 := update f35 (fun j ↦ f24 (48+j)) 251 8
  have w36 : Window s36 f36 305 := window_store_bounded (by decide) w35 w24
    (by decide) (by decide) g36 value36
  have sp36 : stackPtr s36=stackPtr initial-504 := (g36.read (n := 64) (r := 4) (by simp)).trans sp35
  have loaded36 := loaded_after call loaded35 sp35 wide36
  have grow36 := fun a h ↦ g36.grow a (grow35 a h)
  have same36 : stackPtr s36=stackPtr s0 := sp36.trans sp0.symm
  have total36 : AgreesExcept (components (stackPtr s0)) s0 s36 := by
    rw [same35] at wide36
    exact (total35.trans wide36).mono (by simp)
  obtain ⟨s37,a37,ready37,e37⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106b29 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 259)) (by decide) rfl rfl).advances ready36
    (programText_slice (programLoaded_codeIn loaded36) 0x6b29 _ (by decide) (by decide +kernel))
    ⟨e36.rip,writable call grow36 sp36 (off := 259) (by decide) (by decide),code_apart call sp36 (off := 259) (len := 8) (pc := 0x6b29) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b31 (by decide)))
  have g37 : AgreesExcept [.mem (stackPtr s36+259) 8,.rip] s36 s37 := by
    have h := e37.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide37 := store_agrees g37 (by decide)
  have value37 : memLoad s37.external (stackPtr s36+259) 64 =
      memLoad s25.external (stackPtr s25+56) 64 := by
    have h : memLoad s37.external (stackPtr s36+259) 64 = (s36.regValue .rsi) := e37.writes
    have reg : s36.regValue .rsi = (memLoad s25.external (stackPtr s25+56) 64) := ((((((((((g27.trans g28).trans g29).trans g30).trans g31).trans g32).trans g33).trans g34).trans g35).trans g36).read (n := 64) (r := 6) (by simp)).trans v26
    rw [h,reg]
  let f37 := update f36 (fun j ↦ f24 (56+j)) 259 8
  have w37 : Window s37 f37 305 := window_store_bounded (by decide) w36 w25
    (by decide) (by decide) g37 value37
  have sp37 : stackPtr s37=stackPtr initial-504 := (g37.read (n := 64) (r := 4) (by simp)).trans sp36
  have loaded37 := loaded_after call loaded36 sp36 wide37
  have grow37 := fun a h ↦ g37.grow a (grow36 a h)
  have same37 : stackPtr s37=stackPtr s0 := sp37.trans sp0.symm
  have total37 : AgreesExcept (components (stackPtr s0)) s0 s37 := by
    rw [same36] at wide37
    exact (total36.trans wide37).mono (by simp)
  obtain ⟨s38,a38,ready38,e38⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106b31 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 267)) (by decide) rfl rfl).advances ready37
    (programText_slice (programLoaded_codeIn loaded37) 0x6b31 _ (by decide) (by decide +kernel))
    ⟨e37.rip,writable call grow37 sp37 (off := 267) (by decide) (by decide),code_apart call sp37 (off := 267) (len := 8) (pc := 0x6b31) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b39 (by decide)))
  have g38 : AgreesExcept [.mem (stackPtr s37+267) 8,.rip] s37 s38 := by
    have h := e38.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide38 := store_agrees g38 (by decide)
  have value38 : memLoad s38.external (stackPtr s37+267) 64 =
      memLoad s28.external (stackPtr s28+64) 64 := by
    have h : memLoad s38.external (stackPtr s37+267) 64 = (s37.regValue .rdi) := e38.writes
    have reg : s37.regValue .rdi = (memLoad s28.external (stackPtr s28+64) 64) := ((((((((g30.trans g31).trans g32).trans g33).trans g34).trans g35).trans g36).trans g37).read (n := 64) (r := 7) (by simp)).trans v29
    rw [h,reg]
  let f38 := update f37 (fun j ↦ f28 (64+j)) 267 8
  have w38 : Window s38 f38 305 := window_store_bounded (by decide) w37 w28
    (by decide) (by decide) g38 value38
  have sp38 : stackPtr s38=stackPtr initial-504 := (g38.read (n := 64) (r := 4) (by simp)).trans sp37
  have loaded38 := loaded_after call loaded37 sp37 wide38
  have grow38 := fun a h ↦ g38.grow a (grow37 a h)
  have same38 : stackPtr s38=stackPtr s0 := sp38.trans sp0.symm
  have total38 : AgreesExcept (components (stackPtr s0)) s0 s38 := by
    rw [same37] at wide38
    exact (total37.trans wide38).mono (by simp)
  obtain ⟨s39,a39,ready39,e39⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106b39 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 275)) (by decide) rfl rfl).advances ready38
    (programText_slice (programLoaded_codeIn loaded38) 0x6b39 _ (by decide) (by decide +kernel))
    ⟨e38.rip,writable call grow38 sp38 (off := 275) (by decide) (by decide),code_apart call sp38 (off := 275) (len := 8) (pc := 0x6b39) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b41 (by decide)))
  have g39 : AgreesExcept [.mem (stackPtr s38+275) 8,.rip] s38 s39 := by
    have h := e39.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide39 := store_agrees g39 (by decide)
  have value39 : memLoad s39.external (stackPtr s38+275) 64 =
      memLoad s30.external (stackPtr s30+72) 64 := by
    have h : memLoad s39.external (stackPtr s38+275) 64 = (s38.regValue .r8) := e39.writes
    have reg : s38.regValue .r8 = (memLoad s30.external (stackPtr s30+72) 64) := (((((((g32.trans g33).trans g34).trans g35).trans g36).trans g37).trans g38).read (n := 64) (r := 8) (by simp)).trans v31
    rw [h,reg]
  let f39 := update f38 (fun j ↦ f30 (72+j)) 275 8
  have w39 : Window s39 f39 305 := window_store_bounded (by decide) w38 w30
    (by decide) (by decide) g39 value39
  have sp39 : stackPtr s39=stackPtr initial-504 := (g39.read (n := 64) (r := 4) (by simp)).trans sp38
  have loaded39 := loaded_after call loaded38 sp38 wide39
  have grow39 := fun a h ↦ g39.grow a (grow38 a h)
  have same39 : stackPtr s39=stackPtr s0 := sp39.trans sp0.symm
  have total39 : AgreesExcept (components (stackPtr s0)) s0 s39 := by
    rw [same38] at wide39
    exact (total38.trans wide39).mono (by simp)
  obtain ⟨s40,a40,ready40,e40⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106b41 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 283)) (by decide) rfl rfl).advances ready39
    (programText_slice (programLoaded_codeIn loaded39) 0x6b41 _ (by decide) (by decide +kernel))
    ⟨e39.rip,writable call grow39 sp39 (off := 283) (by decide) (by decide),code_apart call sp39 (off := 283) (len := 8) (pc := 0x6b41) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b49 (by decide)))
  have g40 : AgreesExcept [.mem (stackPtr s39+283) 8,.rip] s39 s40 := by
    have h := e40.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide40 := store_agrees g40 (by decide)
  have value40 : memLoad s40.external (stackPtr s39+283) 64 =
      memLoad s32.external (stackPtr s32+80) 64 := by
    have h : memLoad s40.external (stackPtr s39+283) 64 = (s39.regValue .r9) := e40.writes
    have reg : s39.regValue .r9 = (memLoad s32.external (stackPtr s32+80) 64) := ((((((g34.trans g35).trans g36).trans g37).trans g38).trans g39).read (n := 64) (r := 9) (by simp)).trans v33
    rw [h,reg]
  let f40 := update f39 (fun j ↦ f32 (80+j)) 283 8
  have w40 : Window s40 f40 305 := window_store_bounded (by decide) w39 w32
    (by decide) (by decide) g40 value40
  have sp40 : stackPtr s40=stackPtr initial-504 := (g40.read (n := 64) (r := 4) (by simp)).trans sp39
  have loaded40 := loaded_after call loaded39 sp39 wide40
  have grow40 := fun a h ↦ g40.grow a (grow39 a h)
  have same40 : stackPtr s40=stackPtr s0 := sp40.trans sp0.symm
  have total40 : AgreesExcept (components (stackPtr s0)) s0 s40 := by
    rw [same39] at wide40
    exact (total39.trans wide40).mono (by simp)
  obtain ⟨s41,a41,ready41,e41⟩ := (mov_r64_m64_effect_step 0x106b49 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl).advances ready40
    (programText_slice (programLoaded_codeIn loaded40) 0x6b49 _ (by decide) (by decide +kernel))
    ⟨e40.rip,readable call grow40 sp40 (off := 152) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b51 (by decide)))
  have g41 : AgreesExcept [.reg 1,.rip] s40 s41 := e41.agrees
  have wide41 : AgreesExcept (components (stackPtr s40)) s40 s41 := g41.mono (by simp [components])
  have w41 : Window s41 f40 305 := window_registers w40 g41 (by simp) (by simp [Component.Covers])
  have v41 : s41.regValue .rcx = (memLoad s40.external (stackPtr s40+152) 64) := e41.writes
  have sp41 : stackPtr s41=stackPtr initial-504 := (g41.read (n := 64) (r := 4) (by simp)).trans sp40
  have loaded41 := loaded_after call loaded40 sp40 wide41
  have grow41 := fun a h ↦ g41.grow a (grow40 a h)
  have same41 : stackPtr s41=stackPtr s0 := sp41.trans sp0.symm
  have total41 : AgreesExcept (components (stackPtr s0)) s0 s41 := by
    rw [same40] at wide41
    exact (total40.trans wide41).mono (by simp)
  obtain ⟨s42,a42,ready42,e42⟩ := (mov_r64_m64_effect_step 0x106b51 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 158)) (by decide) rfl rfl).advances ready41
    (programText_slice (programLoaded_codeIn loaded41) 0x6b51 _ (by decide) (by decide +kernel))
    ⟨e41.rip,readable call grow41 sp41 (off := 158) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b59 (by decide)))
  have g42 : AgreesExcept [.reg 2,.rip] s41 s42 := e42.agrees
  have wide42 : AgreesExcept (components (stackPtr s41)) s41 s42 := g42.mono (by simp [components])
  have w42 : Window s42 f40 305 := window_registers w41 g42 (by simp) (by simp [Component.Covers])
  have v42 : s42.regValue .rdx = (memLoad s41.external (stackPtr s41+158) 64) := e42.writes
  have sp42 : stackPtr s42=stackPtr initial-504 := (g42.read (n := 64) (r := 4) (by simp)).trans sp41
  have loaded42 := loaded_after call loaded41 sp41 wide42
  have grow42 := fun a h ↦ g42.grow a (grow41 a h)
  have same42 : stackPtr s42=stackPtr s0 := sp42.trans sp0.symm
  have total42 : AgreesExcept (components (stackPtr s0)) s0 s42 := by
    rw [same41] at wide42
    exact (total41.trans wide42).mono (by simp)
  obtain ⟨s43,a43,ready43,e43⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106b59 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 291)) (by decide) rfl rfl).advances ready42
    (programText_slice (programLoaded_codeIn loaded42) 0x6b59 _ (by decide) (by decide +kernel))
    ⟨e42.rip,writable call grow42 sp42 (off := 291) (by decide) (by decide),code_apart call sp42 (off := 291) (len := 8) (pc := 0x6b59) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b61 (by decide)))
  have g43 : AgreesExcept [.mem (stackPtr s42+291) 8,.rip] s42 s43 := by
    have h := e43.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide43 := store_agrees g43 (by decide)
  have value43 : memLoad s43.external (stackPtr s42+291) 64 =
      memLoad s40.external (stackPtr s40+152) 64 := by
    have h : memLoad s43.external (stackPtr s42+291) 64 = (s42.regValue .rcx) := e43.writes
    have reg : s42.regValue .rcx = (memLoad s40.external (stackPtr s40+152) 64) := (g42.read (n := 64) (r := 1) (by simp)).trans v41
    rw [h,reg]
  let f43 := update f40 (fun j ↦ f40 (152+j)) 291 8
  have w43 : Window s43 f43 305 := window_store_bounded (by decide) w42 w40
    (by decide) (by decide) g43 value43
  have sp43 : stackPtr s43=stackPtr initial-504 := (g43.read (n := 64) (r := 4) (by simp)).trans sp42
  have loaded43 := loaded_after call loaded42 sp42 wide43
  have grow43 := fun a h ↦ g43.grow a (grow42 a h)
  have same43 : stackPtr s43=stackPtr s0 := sp43.trans sp0.symm
  have total43 : AgreesExcept (components (stackPtr s0)) s0 s43 := by
    rw [same42] at wide43
    exact (total42.trans wide43).mono (by simp)
  obtain ⟨s44,a44,ready44,e44⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x106b61 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 297)) (by decide) rfl rfl).advances ready43
    (programText_slice (programLoaded_codeIn loaded43) 0x6b61 _ (by decide) (by decide +kernel))
    ⟨e43.rip,writable call grow43 sp43 (off := 297) (by decide) (by decide),code_apart call sp43 (off := 297) (len := 8) (pc := 0x6b61) (n := 8) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b69 (by decide)))
  have g44 : AgreesExcept [.mem (stackPtr s43+297) 8,.rip] s43 s44 := by
    have h := e44.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide44 := store_agrees g44 (by decide)
  have value44 : memLoad s44.external (stackPtr s43+297) 64 =
      memLoad s41.external (stackPtr s41+158) 64 := by
    have h : memLoad s44.external (stackPtr s43+297) 64 = (s43.regValue .rdx) := e44.writes
    have reg : s43.regValue .rdx = (memLoad s41.external (stackPtr s41+158) 64) := (g43.read (n := 64) (r := 2) (by simp)).trans v42
    rw [h,reg]
  let f44 := update f43 (fun j ↦ f40 (158+j)) 297 8
  have w44 : Window s44 f44 305 := window_store_bounded (by decide) w43 w41
    (by decide) (by decide) g44 value44
  have sp44 : stackPtr s44=stackPtr initial-504 := (g44.read (n := 64) (r := 4) (by simp)).trans sp43
  have loaded44 := loaded_after call loaded43 sp43 wide44
  have grow44 := fun a h ↦ g44.grow a (grow43 a h)
  have same44 : stackPtr s44=stackPtr s0 := sp44.trans sp0.symm
  have total44 : AgreesExcept (components (stackPtr s0)) s0 s44 := by
    rw [same43] at wide44
    exact (total43.trans wide44).mono (by simp)
  obtain ⟨s45,a45,ready45,e45⟩ := (CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x106b69 0 (.sib 4 none 0 (.d32 243)) (by decide) rfl rfl).advances ready44
    (programText_slice (programLoaded_codeIn loaded44) 0x6b69 _ (by decide) (by decide +kernel))
    ⟨e44.rip,writable call grow44 sp44 (off := 243) (by decide) (by decide),code_apart call sp44 (off := 243) (len := 4) (pc := 0x6b69) (n := 7) (by decide) (by decide)⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x6b70 (by decide)))
  have g45 : AgreesExcept [.mem (stackPtr s44+243) 4,.rip] s44 s45 := by
    have h := e45.agrees
    x86_norm [movM64R64Effect,CrossPageStore.movM32R32LegacyEffect,movM16R16Effect,stackPtr] at h ⊢
    exact h
  have wide45 := store_agrees g45 (by decide)
  have value45 : memLoad s45.external (stackPtr s44+243) 32 =
      memLoad s4.external (stackPtr s4+171) 32 := by
    have h : memLoad s45.external (stackPtr s44+243) 32 = (s44.regValue .rax).setWidth 32 := e45.writes
    have reg : s44.regValue .rax = (memLoad s4.external (stackPtr s4+171) 32).setWidth 64 := (((((((((((((((((((((((((((((((((((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).trans g20).trans g21).trans g22).trans g23).trans g24).trans g25).trans g26).trans g27).trans g28).trans g29).trans g30).trans g31).trans g32).trans g33).trans g34).trans g35).trans g36).trans g37).trans g38).trans g39).trans g40).trans g41).trans g42).trans g43).trans g44).read (n := 64) (r := 0) (by simp)).trans v5
    rw [h,reg]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32≤64),BitVec.setWidth_eq]
  let f45 := update f44 (fun j ↦ f4 (171+j)) 243 4
  have w45 : Window s45 f45 305 := window_store_bounded (by decide) w44 w4
    (by decide) (by decide) g45 value45
  have sp45 : stackPtr s45=stackPtr initial-504 := (g45.read (n := 64) (r := 4) (by simp)).trans sp44
  have loaded45 := loaded_after call loaded44 sp44 wide45
  have grow45 := fun a h ↦ g45.grow a (grow44 a h)
  have same45 : stackPtr s45=stackPtr s0 := sp45.trans sp0.symm
  have total45 : AgreesExcept (components (stackPtr s0)) s0 s45 := by
    rw [same44] at wide45
    exact (total44.trans wide45).mono (by simp)
  exact ⟨s45,((((((((((((((((((((((((((((((((((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16).trans a17).trans a18).trans a19).trans a20).trans a21).trans a22).trans a23).trans a24).trans a25).trans a26).trans a27).trans a28).trans a29).trans a30).trans a31).trans a32).trans a33).trans a34).trans a35).trans a36).trans a37).trans a38).trans a39).trans a40).trans a41).trans a42).trans a43).trans a44).trans a45),ready45,loaded45,w45,e45.rip,total45⟩

end P256.Proofs.EcdhWrapper.Peer.Buffer
