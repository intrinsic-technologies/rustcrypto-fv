import P256.Proofs.Program.LimbSelect.Memory
import P256.Proofs.Program.State
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program (CalleeResult boundary_ne_program inProgram_of_textOffset memoryRegion_contains_add programLoaded_codeIn programText_slice stack_region_end inProgram_low)

namespace P256.Proofs.Program.LimbSelect

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem return_slot [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (hp : Pre s boundary) (h : AgreesExcept (components s 4) s t) :
    (Operand.mem (stackPtr s) : Operand 64).read t =
      (Operand.mem (stackPtr s) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  have he : t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 i]? := by
    apply h.byte
    intro c hm hv
    simp only [components, registers, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;>
      try exact hv.elim
    · obtain ⟨j, hj, he⟩ := hv
      have hn := congrArg BitVec.toNat he
      have hb := P256.Proofs.Program.stack_bounds hp.stack
      have hs := P256.Proofs.Program.stack_sub_toNat hp.stack (offset := 72) (by decide)
      change (stackPtr s - 72).toNat = (stackPtr s).toNat - 72 at hs
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega), hs] at hn
      omega
    · obtain ⟨j, hj, he⟩ := hv
      have hsep := hp.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
      apply hsep _ (output_contains hp hj)
      rw [← he]
      apply memoryRegion_contains_add hp.stack.1 (len := 8) _ _ hi
      · change (stackPtr s).toNat - 80 ≤ (stackPtr s).toNat
        omega
      · rw [stack_region_end]
        exact Nat.le_refl _
  exact congrArg (fun o : Option UInt8 => o.getD 0) he

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {select : Bool}
    (hp : Pre s boundary) (h : LoopState s t select 4)
    (hrip : t.RIP = 0x11920a) (hexec : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 32 80 ∧ SelectedBytesAt s u select := by
  have hc := programLoaded_codeIn (h.loaded hp (by decide))
  obtain ⟨u, hau, hru, heu⟩ :=
    (add_r64_imm8_effect_step 0x11920a 0x48 0xc4 72 (by constructor <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)).advances h.ready
      (programText_slice hc 0x1920a [0x48, 0x83, 0xc4, 0x48] (by decide +kernel) rfl)
      hrip (boundary_ne_program hp.outerBoundary
        (inProgram_of_textOffset 0x1920e (by decide +kernel)))
  change (addR64Imm8Effect 0x11920a 4 72 t).Holds t u at heu
  have hspu : stackPtr u = stackPtr s := by
    have hw : stackPtr u = stackPtr t + 72 := heu.writes
    rw [hw]
    change t.regValue .rsp + 72 = s.regValue .rsp
    rw [h.rsp, BitVec.sub_add_cancel]
  have hagu : AgreesExcept (components s 4) s u :=
    (h.agrees.trans heu.agrees).mono (by simp [components, registers])
  have htop : stackTop u = (returnBoundary s).rip := by
    rw [stackTop, hspu]
    exact return_slot hp hagu
  have hread : MemReadable u (stackPtr u) 8 := by
    rw [hspu]
    apply P256.Proofs.Program.readable_of_grow _ hagu.grow
    simpa only [BitVec.sub_zero] using
      P256.Proofs.Program.stack_sub_readable hp.stack (offset := 0) (len := 8)
        (by decide) (by decide)
  have hcu := programLoaded_codeIn (loaded_of_agrees hp (by decide) hagu)
  obtain ⟨v, hav, hrv, hev⟩ := (ret_effect_step 0x11920e).advances hru
    (programText_slice hcu 0x1920e [0xc3] (by decide +kernel) rfl)
    ⟨⟨heu.rip, hread⟩, htop ▸ inProgram_low hp.returnInProgram⟩
    (by change stackTop u ≠ boundary.rip
        rw [htop]
        exact boundary_ne_program hp.outerBoundary hp.returnInProgram)
  have hagv : AgreesExcept (components s 4) s v :=
    (hagu.trans hev.agrees).mono (by simp [components, registers])
  obtain ⟨fuel, hf⟩ := hexec
  refine ⟨v, ⟨⟨fuel + 1 + 1, (hf.trans hau).trans hav⟩, hev.rip.trans htop, ?_,
    bindingsSupported_of_ready_agrees hp.bindingsSupported hrv hagv,
    supportedMachine_of_ready_agrees hp.machine hrv hagv, ?_,
    hagv.directionFlagClear (by simp [components, registers]) hp.directionFlag,
    hagv.mxcsr (by simp [components, registers]), hagv.fcw (by simp [components, registers]),
    hagv.memoryWriteFrame (components_within hp (by decide)),
    loaded_of_agrees hp (by decide) hagv, hagv.grow⟩, ?_⟩
  · have hw : stackPtr v = stackPtr u + 8 := hev.writes
    change stackPtr v = stackPtr s + 8
    rw [hw, hspu]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hagv.read (r := 3) (n := 64) (by simp [components, registers])
    · exact hagv.read (r := 5) (n := 64) (by simp [components, registers])
    · exact hagv.read (r := 12) (n := 64) (by simp [components, registers])
    · exact hagv.read (r := 13) (n := 64) (by simp [components, registers])
    · exact hagv.read (r := 14) (n := 64) (by simp [components, registers])
    · exact hagv.read (r := 15) (n := 64) (by simp [components, registers])
  · intro i hi
    exact ((heu.agrees.trans hev.agrees).byte (by simp [Component.Covers])).trans
      (h.selected i hi)

end P256.Proofs.Program.LimbSelect
