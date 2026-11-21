import P256.Proofs.Signing.Wrapper.Finish.Capacity
import X86Proofs.Instructions.Mov.Triple
import P256.Proofs.Common.Instructions.CrossPageStore.Immediate

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish_store [Bindings] {initial t : RamState} (pre : Pre initial)
    (state : State initial t) (rip : t.RIP = 0x102b10) (output : t.regValue .r11 = initial.regValue .rcx) :
    ∃ u, Advances (returnBoundary initial) 2 t u ∧ State initial u ∧
      u.RIP = 0x102b19 ∧ u.regValue .rax = 0 ∧
      memLoad u.external (initial.regValue .rcx) 64 = 64 ∧
      AgreesExcept [.mem (initial.regValue .rcx) 8,.reg 0,.flags,.rip] t u := by
  have addr : storeAddrAt 0x102b10 (.base 11 .none) 7 t = t.regValue .r11 := by
    change t.regValue .r11 + 0 = t.regValue .r11
    exact BitVec.add_zero _
  have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable t
      (initial.regValue .rcx) 8 := by
    simpa only [BitVec.add_zero] using (output_writable pre state).add 0 (len := 8) (by decide)
  have apart : RangeApart (initial.regValue .rcx) 8 0x102b10 7 := by
    simpa only [BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
      P256.Proofs.Common.Instructions.RangeApart.add_left
        (h := output_code pre (offset := 0x2b10) (len := 7) (by decide)) 0 (len := 8) (by decide)
  obtain ⟨a, ha, ra, ea⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any
      0x102b10 0x49 (by simp [RexWPrefix]) (.base 11 .none) (by decide) rfl rfl 64).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x2b10 _
        (by decide) (by decide +kernel))
      ⟨rip, by change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (storeAddrAt _ _ 7 t) 8
               rw [addr,output]; exact writable,
        by change RangeApart (storeAddrAt _ _ 7 t) 8 0x102b10 7
           rw [addr,output]; exact apart⟩
      (boundary_ne_program pre.outside (inProgram_of_textOffset 0x2b17 (by decide)))
  change (movM64Imm32Effect 0x102b10 (.base 11 .none) 64 t).Holds t a at ea
  have fa : AgreesExcept [.mem (initial.regValue .rcx) 8,.rip] t a := by
    have f : AgreesExcept [.mem (storeAddrAt 0x102b10 (.base 11 .none) 7 t) 8,.rip] t a := by
      simpa only [movM64Imm32Effect_components,AddrMode.tail,Disp.bytes,
        List.length_nil,Nat.add_zero] using ea.agrees
    simpa only [addr,output] using f
  have writes : WritesWithin [.mem (initial.regValue .rcx) 8,.rip]
      #v[registerRegion initial .rcx 72] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_,by simp,output_contains pre (off := 0) (len := 8) (by decide)
        (by simpa only [BitVec.add_zero] using ha)⟩
    · exact ha.elim
  have sa := after pre state ra fa writes (by simp) (by simp)
  have word : memLoad a.external (initial.regValue .rcx) 64 = 64 := by
    have h := ea.writes
    change memLoad a.external (storeAddrAt 0x102b10 (.base 11 .none) 7 t) 64 = 64 at h
    simpa only [addr,output] using h
  obtain ⟨u, hu, ru, eu⟩ := (mov_r32_r32_effect_step 0x102b17 0xe8 (by decide)).advances ra
    (programText_slice (programLoaded_codeIn sa.loaded) 0x2b17 _ (by decide) (by decide +kernel))
    ea.rip (boundary_ne_program pre.outside (inProgram_of_textOffset 0x2b19 (by decide)))
  have fu : AgreesExcept [.reg 0,.rip] a u := eu.agrees
  have mu := fu.external (by simp [Component.Covers])
  refine ⟨u,ha.trans hu,sa.after_registers ru fu (by simp [Component.Covers]) (by simp) (by simp),
    eu.rip,?_,by rw [mu]; exact word,(fa.trans fu).mono (by simp)⟩
  have h := eu.writes
  change u.regValue .rax = ((a.regValue .rbp).setWidth 32).setWidth 64 at h
  simpa only [sa.rbp,BitVec.setWidth_zero,BitVec.ofNat_eq_ofNat] using h

end P256.Proofs.Signing.Wrapper.Finish
