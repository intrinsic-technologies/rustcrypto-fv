import P256.Proofs.Program.Compare.Frame.Epilogue
import P256.Proofs.Program.Compare.Boundary

namespace P256.Proofs.Program.Compare.Frame

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

private theorem tail_boundary_ne {boundary : ReturnBoundary} (h : ¬ InProgram boundary.rip)
    {ip : BitVec 64} (hi : InRoutine ip) : ip ≠ boundary.rip := by
  intro he
  exact h (he ▸ inRoutine_inProgram hi)

theorem tail_push_pre [Bindings] {initial s : RamState} (h : CallPre initial)
    (hip : s.RIP = 0x11c8c9) (hsp : stackPtr s = stackPtr initial - 56)
    (hgrow : ∀ x : BitVec 64, (initial.external[x]?).isSome → (s.external[x]?).isSome) :
    PushPre 0x11c8c9 5 s ∧
      (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Avoids Extracted.programSections.toCodeMap := by
  have ha : pushAddr s = stackPtr initial - 64 := by
    rw [pushAddr, hsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have hw := h.frame.stack_sub_writable8 (offset := 64) (by decide +kernel) (by decide +kernel)
  have hw' : MemWritable s (pushAddr s) 8 := by
    rw [ha]
    exact ⟨hw.low, fun i hi ↦ hgrow _ (hw.mem i hi), hw.tables⟩
  have hn (i : Nat) (hi : i < 8) : ¬ InProgram (pushAddr s + BitVec.ofNat 64 i) := by
    rw [ha]
    exact h.frame.stack_sub_avoids_code (offset := 64) (len := 8)
      (by decide +kernel) (by decide +kernel) hi
  refine ⟨⟨hip, hw', ?_⟩, ?_⟩
  · intro i hi j hj he
    apply hn i hi
    rw [he]
    have hs : 0x1c8ce ≤ Extracted.textBytes.size := by decide +kernel
    obtain ⟨byte, hm⟩ := text_program_mem_of_offset (0x1c8c9 + j) (by omega)
    have hm := P256.Proofs.Program.Compare.inProgram_of_mem hm
    simpa only [InProgram, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] using hm
  · intro x hx c hc hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨i, hi, he⟩ := hcov
      apply hn i hi
      rw [← he]
      exact P256.Proofs.Program.Compare.inProgram_of_mem hx
    · exact hcov

theorem tail_call [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hp : PushPre 0x11c8c9 5 s)
    (havoid : (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Avoids Extracted.programSections.toCodeMap)
    (hout : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programSections.toCodeMap t ∧
      (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Holds s t := by
  have hb : CodeIn (codeRange 0x11c8c9 (encodeCallRel32 0x462)) s :=
    program_text_slice hc 0x1c8c9 5 (by decide +kernel)
  have hs : StepEffect (PushPre 0x11c8c9 5) (codeRange 0x11c8c9 (encodeCallRel32 0x462))
      (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce) :=
    call_rel32_effect_step 0x11c8c9 0x462 (by decide +kernel)
  obtain ⟨t, ha, ht, he⟩ := hs.advances hr hb hp
    (by
      change (0x11cd30 : BitVec 64) ≠ boundary.rip
      exact tail_boundary_ne hout (by constructor <;> decide +kernel))
  exact ⟨t, ha, ht, he.codeIn havoid hc, he⟩

theorem tail_call_of_callPre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (h : CallPre initial) (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hip : s.RIP = 0x11c8c9) (hSaved : Saved initial s)
    (hgrow : ∀ x : BitVec 64, (initial.external[x]?).isSome → (s.external[x]?).isSome)
    (hout : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programSections.toCodeMap t ∧
      (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Holds s t := by
  obtain ⟨hp, hav⟩ := tail_push_pre h hip hSaved.rsp hgrow
  exact tail_call hr hc hp hav hout

theorem tail_return [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hip : s.RIP = 0x11ce9e ∨ s.RIP = 0x11ce0d)
    (hread : MemReadable s (stackPtr s) 8) (htop : stackTop s = 0x11c8ce)
    (hout : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programSections.toCodeMap t ∧
      (retEffect s).Holds s t := by
  have hb : CodeIn (codeRange s.RIP [0xc3]) s := by
    rcases hip with hip | hip
    · rw [hip]
      exact program_text_slice hc 0x1ce9e 1 (by decide +kernel)
    · rw [hip]
      exact program_text_slice hc 0x1ce0d 1 (by decide +kernel)
  obtain ⟨t, ha, ht, he⟩ := (ret_effect_step s.RIP).advances hr hb
    ⟨⟨rfl, hread⟩, by rw [htop]; decide +kernel⟩ (by
      change stackTop s ≠ boundary.rip
      rw [htop]
      exact tail_boundary_ne hout (by constructor <;> decide +kernel))
  exact ⟨t, ha, ht, he.codeIn
    (Effect.avoids_of_components_reg_rip (retEffect_components s) _) hc, he⟩

theorem tail_return_after_call [Bindings] {s called body : RamState} {boundary : ReturnBoundary}
    (hcall : (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Holds s called)
    (hread : MemReadable s (pushAddr s) 8)
    (hr : ReadyToStep body) (hc : CodeIn Extracted.programSections.toCodeMap body)
    (hip : body.RIP = 0x11ce9e ∨ body.RIP = 0x11ce0d)
    (hmem : body.external = called.external) (hsp : stackPtr body = stackPtr called)
    (hout : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 body t ∧ ReadyToStep t ∧ CodeIn Extracted.programSections.toCodeMap t ∧
      (retEffect body).Holds body t := by
  have hs : stackPtr called = pushAddr s := hcall.writes.1
  have hb : MemReadable body (stackPtr body) 8 := by
    rw [hsp, hs]
    have hrc := hread.of_holds hcall
    exact ⟨hrc.low, fun i hi ↦ hmem ▸ hrc.mem i hi⟩
  have ht : stackTop body = 0x11c8ce := by
    rw [stackTop, hsp]
    change memLoad body.external (stackPtr called) 64 = _
    rw [hmem]
    exact (callEffect_stack hcall).1
  exact tail_return hr hc hip hb ht hout

theorem tail_call_read_mem {s called : RamState} {address : BitVec 64} {width : Nat}
    (h : (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Holds s called)
    (ha : RangeApart (pushAddr s) 8 address (width / 8)) :
    (Operand.mem address : Operand width).read called =
      (Operand.mem address : Operand width).read s := by
  apply memLoad_congr
  intro i hi
  change (called.external[address + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[address + BitVec.ofNat 64 i]?).getD 0
  rw [h.agrees.byte]
  intro c hc hcov
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcov
  · obtain ⟨j, hj, he⟩ := hcov
    exact ha j hj i hi he.symm
  · exact hcov

theorem tail_call_saved_word {s called : RamState} {offset : BitVec 64}
    (h : (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Holds s called)
    (hoff : offset = 16 ∨ offset = 24 ∨ offset = 32 ∨ offset = 40 ∨
      offset = 48 ∨ offset = 56) :
    (Operand.mem (stackPtr s + offset) : Operand 64).read called = word s offset := by
  apply tail_call_read_mem h
  have ha : OffsetsApart (-8) 8 offset 8 := by
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl <;>
      unfold OffsetsApart <;> decide +kernel
  intro i hi j hj
  simpa [pushAddr, BitVec.sub_eq_add_neg] using
    ha.ne (stackPtr s) hi hj (by decide +kernel)

theorem Saved.after_tail_call {initial s called t : RamState} (hs : Saved initial s)
    (hcall : (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Holds s called)
    (hm : t.external = called.external) (hsp : stackPtr t = stackPtr s)
    (h13 : t.regValue .r13 = s.regValue .r13) : Saved initial t := by
  have hw (offset : BitVec 64)
      (hoff : offset = 16 ∨ offset = 24 ∨ offset = 32 ∨ offset = 40 ∨
        offset = 48 ∨ offset = 56) : word t offset = word s offset := by
    change memLoad t.external (stackPtr t + offset) 64 = _
    rw [hm, hsp]
    exact tail_call_saved_word hcall hoff
  exact ⟨hsp.trans hs.rsp, (hw 16 (by simp)).trans hs.rbx,
    (hw 48 (by simp)).trans hs.rbp, (hw 24 (by simp)).trans hs.r12,
    h13.trans hs.r13, (hw 32 (by simp)).trans hs.r14,
    (hw 40 (by simp)).trans hs.r15⟩

theorem tail_call_return_word {s called t : RamState}
    (hcall : (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Holds s called)
    (hm : t.external = called.external) (hsp : stackPtr t = stackPtr s) :
    word t 56 = word s 56 := by
  change memLoad t.external (stackPtr t + 56) 64 = _
  rw [hm, hsp]
  exact tail_call_saved_word hcall (by simp)

theorem tail_call_readable {s called t : RamState} {address : BitVec 64} {length : Nat}
    (hcall : (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Holds s called)
    (hm : t.external = called.external) (hread : MemReadable s address length) :
    MemReadable t address length :=
  (hread.of_holds hcall).of_external_eq hm

end P256.Proofs.Program.Compare.Frame
