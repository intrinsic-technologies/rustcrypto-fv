import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Generate.Wrapper.Tail.OutputSafety
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem finish_store [Bindings] {initial t : RamState} {input : ByteArray} {slices : Array Input} {d : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (state : OutputState initial t input) (rip : t.RIP = 0x106ed9)
    (count : t.regValue .r15 = 97)
    (outside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ u, OutputState initial u input ∧ u.RIP = 0x106ede ∧ u.regValue .rax = 0 ∧
      memLoad u.external (initial.regValue .rcx) 64 = 97 ∧
      AgreesExcept [.reg 0,.flags,.mem (initial.regValue .rcx) 8,.rip] t u := by
  have addr : storeAddrAt 0x106ed9 (.base 14 .none) 3 t = t.regValue .r14 := by
    change t.regValue .r14 + 0 = t.regValue .r14
    exact BitVec.add_zero _
  have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable t
      (initial.regValue .rcx) 8 := by
    simpa only [BitVec.add_zero] using (output_writable call draw state.allocated).add 0 (len := 8) (by decide)
  have apart : RangeApart (initial.regValue .rcx) 8 0x106ed9 3 := by
    simpa only [BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using
      output_code call draw (off := 0) (len := 8) (codeOffset := 0x6ed9) (codeLen := 3)
        (by decide) (by decide)
  obtain ⟨a, ha, ra, ea⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any
      0x106ed9 0x4d (by simp [RexWPrefix]) 15 (.base 14 .none) (by decide) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x6ed9 _
        (by decide) (by decide +kernel))
      ⟨rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (storeAddrAt _ _ 3 t) 8
        rw [addr,state.output]
        exact writable, by
        change RangeApart (storeAddrAt _ _ 3 t) 8 0x106ed9 3
        rw [addr,state.output]
        exact apart⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x6edc (by decide)))
  change (storeEffect (n := 64) 0x106ed9 3 (storeAddrAt 0x106ed9 (.base 14 .none) 3)
    (fun v => (Operand.reg 15 : Operand 64).read v) t).Holds t a at ea
  have fa : AgreesExcept [.mem (initial.regValue .rcx) 8,.rip] t a := by
    have f : AgreesExcept [.mem (storeAddrAt 0x106ed9 (.base 14 .none) 3 t) 8,.rip] t a := by
      simpa only [storeEffect_components,Nat.reduceDiv] using ea.agrees
    simpa only [addr,state.output] using f
  have writes : WritesWithin [.mem (initial.regValue .rcx) 8,.rip]
      #v[outputRegion signingKeyGenerateFromRng initial [input],workRegion initial] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_,by simp,output_contains call draw (off := 0) (len := 8) (by decide)
        (by simpa only [BitVec.add_zero] using ha)⟩
    · exact ha.elim
  have sa := after_output_effect call state ha ra fa writes
    ((fa.read (n := 64) (r := 4) (by simp)).trans state.rsp) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp) (by simp)
  have word : memLoad a.external (initial.regValue .rcx) 64 = 97 := by
    have h := ea.writes
    change memLoad a.external (storeAddrAt 0x106ed9 (.base 14 .none) 3 t) 64 = t.regValue .r15 at h
    simpa only [addr,state.output,count] using h
  obtain ⟨u, hu, ru, eu⟩ := (xor_r32_r32_effect_step 0x106edc 0xc0 (by decide)).advances ra
    (programText_slice (programLoaded_codeIn sa.loaded) 0x6edc _ (by decide) (by decide +kernel))
    ea.rip (boundary_ne_program outside (inProgram_of_textOffset 0x6ede (by decide)))
  have fu : AgreesExcept [.reg 0,.flags,.rip] a u := eu.agrees
  have mu := fu.external (by simp [Component.Covers])
  refine ⟨u,sa.after_registers hu ru fu (by simp [Component.Covers]) (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (by simp),eu.rip,?_,?_,
    (fa.trans fu).mono (by simp)⟩
  · have h := eu.writes
    change u.regValue .rax = (((Operand.reg 0 : Operand 32).read a) ^^^ ((Operand.reg 0 : Operand 32).read a)).setWidth 64 at h
    simpa only [BitVec.xor_self,BitVec.setWidth_zero,BitVec.ofNat_eq_ofNat] using h
  · rw [mu]
    exact word

end P256.Proofs.Generate.Wrapper.Finish
