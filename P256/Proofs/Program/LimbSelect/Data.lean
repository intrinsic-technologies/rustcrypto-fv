import P256.Proofs.Program.LimbSelect.Memory

set_option autoImplicit false

namespace P256.Proofs.Program.LimbSelect

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {select : Bool} {count : Nat}

theorem source_word (hp : Pre s boundary) (hc : count < 4)
    (h : AgreesExcept (components s count) s t) :
    (Operand.mem (s.regValue .rdx + BitVec.ofNat 64 (8*count)) : Operand 64).read t =
    (Operand.mem (s.regValue .rdx + BitVec.ofNat 64 (8*count)) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  rw [add_ofNat_add_ofNat]
  exact congrArg (fun o : Option UInt8 => o.getD 0) (source_byte hp (by omega) h (by omega))

theorem output_word (hp : Pre s boundary) (hc : count < 4)
    (h : AgreesExcept (components s count) s t) :
    (Operand.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) : Operand 64).read t =
    (Operand.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  rw [add_ofNat_add_ofNat]
  exact congrArg (fun o : Option UInt8 => o.getD 0)
    (output_byte hp (by omega) h (by omega) (by omega))

omit [Bindings] in
theorem append_agrees (h : AgreesExcept (components s count) s t)
    (he : AgreesExcept (registers ++
      [.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) 8]) t u) :
    AgreesExcept (components s (count+1)) s u := by
  apply (h.trans he).widen
  · intro c hc hm
    simp only [components, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with (hc | (rfl | rfl)) | (hc | rfl)
    · exact Or.inl hc
    · simp_all [Component.isMem]
    · simp_all [Component.isMem]
    · exact Or.inl hc
    · simp_all [Component.isMem]
  · intro a c hc hv
    simp only [components, registers, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) |
      ((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) <;> try exact hv.elim
    · exact ⟨_, by simp [components], hv⟩
    · obtain ⟨i, hi, rfl⟩ := hv
      exact ⟨.mem (s.regValue .rdi) (8*(count+1)), by simp [components],
        i, by omega, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := hv
      exact ⟨.mem (s.regValue .rdi) (8*(count+1)), by simp [components],
        8*count+i, by omega, by rw [add_ofNat_add_ofNat]⟩

theorem selected_append (hp : Pre s boundary) (hc : count < 4)
    (h : LoopState s t select count)
    (he : AgreesExcept (registers ++
      [.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) 8]) t u)
    (hw : (Operand.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) : Operand 64).read u =
      if select then (Operand.mem (s.regValue .rdx + BitVec.ofNat 64 (8*count)) : Operand 64).read s
      else (Operand.mem (s.regValue .rdi + BitVec.ofNat 64 (8*count)) : Operand 64).read s) :
    ∀ i < 8*(count+1), u.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      if select then s.external[s.regValue .rdx + BitVec.ofNat 64 i]?
      else s.external[s.regValue .rdi + BitVec.ofNat 64 i]? := by
  intro i hi
  by_cases hold : i < 8*count
  · refine (he.byte ?_).trans (h.selected i hold)
    intro c hm hv
    simp only [registers, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;> try exact hv.elim
    obtain ⟨j, hj, hjEq⟩ := hv
    rw [add_ofNat_add_ofNat] at hjEq
    have hb : (s.regValue .rdi).toNat + 32 < 2^32 := hp.outputBounded
    have hn := congrArg BitVec.toNat hjEq
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
    omega
  · have hio : i = 8*count+(i-8*count) := by omega
    have hg := (h.agrees.trans he).grow
    have hdest : (u.external[s.regValue .rdi + BitVec.ofNat 64 i]?).isSome :=
      hg _ (Option.isSome_iff_exists.mpr (hp.outputAllocated _ (output_contains hp (by omega))))
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hdest
    cases select <;> simp only [Bool.false_eq_true, ↓reduceIte] at hw ⊢
    · obtain ⟨a, ha⟩ := hp.outputAllocated _ (output_contains hp (show i < 32 by omega))
      have hh := memByte_of_memLoad_eq hw (i-8*count) (by omega)
      simp only [add_ofNat_add_ofNat, ← hio] at hh
      have hab : b = a := by simpa only [memByte, PhysicalMemory.read, hb, ha, Option.getD_some] using hh
      rw [hb, ha, hab]
    · obtain ⟨a, ha⟩ := hp.sourceAllocated _ (source_contains hp (show i < 32 by omega))
      have hh := memByte_of_memLoad_eq hw (i-8*count) (by omega)
      simp only [add_ofNat_add_ofNat, ← hio] at hh
      have hab : b = a := by simpa only [memByte, PhysicalMemory.read, hb, ha, Option.getD_some] using hh
      rw [hb, ha, hab]

end P256.Proofs.Program.LimbSelect
