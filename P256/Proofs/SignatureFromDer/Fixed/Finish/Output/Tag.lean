import P256.Proofs.SignatureFromDer.Fixed.Finish.Output.Memory

set_option autoImplicit false

open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.SignatureFromDer.Fixed.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem store_tag [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {inputBytes : Nat} (pre : CalleePre s boundary 0x109ac0 inputBytes 72 560) (state : Stage s t boundary)
    (p : BitVec 64) (tag : BitVec 32)
    (code : CodeIn (codeRange p ([0x48, 0xc7, 0x03] ++ immBytes 32 tag)) t)
    (rip : t.RIP = p) (next : InProgram (p + 7#64))
    (apart : RangeApart (s.regValue .rdi) 8 p 7) :
    ∃ u, Stage s u boundary ∧ u.RIP = p + 7#64 ∧
      loadBytes u.external (s.regValue .rdi) 8 = .ok (tag.signExtend 64) ∧
      AgreesExcept [.mem (s.regValue .rdi) 8, .rip] t u := by
  have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi) 8 := by
    simpa only [BitVec.add_zero] using (output_writable pre state.toFrame).add 0 (len := 8) (by decide)
  have address (v : RamState) : storeAddrAt p (.base 3 .none) 7 v = v.regValue .rbx := by
    change v.regValue .rbx + 0#64 = v.regValue .rbx
    exact BitVec.add_zero _
  obtain ⟨u, run, ready, effect⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any p 0x48 (by simp [RexWPrefix])
      (.base 3 .none) (by decide) rfl rfl tag).advances
      (readyToStep state.machine state.bindingsSupported)
      code
      ⟨rip, by change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (storeAddrAt _ _ 7 t) 8
               rw [address, state.output]; exact writable,
        by change RangeApart (storeAddrAt _ _ 7 t) 8 p 7
           rw [address, state.output]; exact apart⟩
      (boundary_ne_program pre.outerBoundary next)
  change (storeEffect (n := 64) p 7 (storeAddrAt p (.base 3 .none) 7)
    (fun _ => tag.signExtend 64) t).Holds t u at effect
  have frame : AgreesExcept [.mem (s.regValue .rdi) 8, .rip] t u := by
    have h : AgreesExcept [.mem (storeAddrAt p (.base 3 .none) 7 t) 8, .rip] t u := by
      simpa only [storeEffect_components, Nat.reduceDiv] using effect.agrees
    simpa only [address, state.output] using h
  have writes : WritesWithin [.mem (s.regValue .rdi) 8, .rip]
      #v[registerRegion s .rdi 72, workRegion s] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨registerRegion s .rdi 72, by simp, ?_⟩
      exact output_contains pre (offset := 0) (len := 8) (by decide) (by simpa only [BitVec.add_zero] using ha)
    · exact ha.elim
  have stateU := state.after pre run ready frame writes
    ((frame.read (n := 64) (r := 4) (by simp)).trans state.rsp) (by simp)
  have word : memLoad u.external (s.regValue .rdi) 64 = tag.signExtend 64 := by
    have h := effect.writes
    change memLoad u.external (storeAddrAt p (.base 3 .none) 7 t) 64 = tag.signExtend 64 at h
    simpa only [address, state.output] using h
  have allocated := (output_writable pre stateU.toFrame).add 0 (len := 8) (by decide)
  have bytes := Bytes.of_memLoad (n := 64) (by
    intro i hi
    simpa only [BitVec.add_zero] using allocated.mem i hi)
  rw [word] at bytes
  exact ⟨u, stateU, effect.rip, bytes.loadBytes64, frame⟩

end P256.Proofs.SignatureFromDer.Fixed.Finish
