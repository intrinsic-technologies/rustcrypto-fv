import P256.Proofs.ReadBe.Call

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}

theorem Pre.call_memcpy_frame (pre : Pre s boundary) (frame : Frame s t)
    (effect : (callEffect (fun _ => 0x11c930) 0x119131 t).Holds t u)
    (destination : t.regValue .rdi = frameBase s + 16)
    (result : CalleeResult u v boundary 8 0) :
    MemoryWriteFrame t v #v[scratchRegion s] := by
  have callFrame : MemoryWriteFrame t u #v[scratchRegion s] := by
    apply effect.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact ha.elim
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨scratchRegion s, by simp, ?_⟩
    rw [frame.push_address]
    exact pre.scratch_contains (offset := 80) (by decide) (by decide) (len := 8) (by decide) hi
  have bounds := (stack_bounds pre.stack)
  have sp : stackPtr u = stackPtr s - 80 := effect.writes.1.trans frame.push_address
  have spNat : (stackPtr u).toNat = (stackPtr s).toNat - 80 := by
    rw [sp]
    exact stack_sub_toNat pre.stack (by decide)
  have dest : u.regValue .rdi = stackPtr s - 56 := by
    have h := (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
    change u.regValue .rdi = (stackPtr s - 72) + 16 at h
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  have destNat : (u.regValue .rdi).toNat = (stackPtr s).toNat - 56 := by
    rw [dest]
    exact stack_sub_toNat pre.stack (by decide)
  apply memoryWriteFrame_trans callFrame
  intro a ha
  apply result.frame a
  intro r hr hin
  apply ha (scratchRegion s) (by simp)
  have hr' : r = registerRegion u .rdi 8 ∨ r = Stack.region u 0 := by simpa using hr
  rcases hr' with rfl | rfl
  · change (u.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (u.regValue .rdi).toNat + 8 at hin
    rw [destNat] at hin
    change (stackPtr s).toNat - 80 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 80 + 32
    constructor <;> omega
  · change (stackPtr u).toNat - 0 ≤ a.toNat ∧
      a.toNat < (Stack.region u 0).start + (Stack.region u 0).size at hin
    rw [stack_region_end, Nat.sub_zero, spNat] at hin
    change (stackPtr s).toNat - 80 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 80 + 32
    constructor <;> omega

omit [Bindings] in
theorem scratch_frame
    (frame : MemoryWriteFrame t u #v[scratchRegion s]) :
    MemoryWriteFrame t u #v[registerRegion s .rdx 32, scratchRegion s] := by
  intro a ha
  apply frame a
  intro r hr
  have he : r = scratchRegion s := by simpa using hr
  subst r
  exact ha _ (by simp)

theorem Frame.after_memcpy (pre : Pre s boundary) (frame : Frame s t)
    (effect : (callEffect (fun _ => 0x11c930) 0x119131 t).Holds t u)
    (destination : t.regValue .rdi = frameBase s + 16)
    (result : CalleeResult u v boundary 8 0) : Frame s v := by
  have localFrame := scratch_frame (pre.call_memcpy_frame frame effect destination result)
  have total := memoryWriteFrame_trans frame.frame (pre.local_frame localFrame)
  refine ⟨?_, result.bindingsSupported, result.machine, result.directionFlag,
    result.mxcsr.trans ((effect.agrees.mxcsr (by simp)).trans frame.mxcsr),
    result.fp87.trans ((effect.agrees.fcw (by simp)).trans frame.fp87),
    total, pre.loaded_of_frame total,
    fun a ha => result.allocated a (effect.agrees.grow a (frame.allocated a ha)), ?_, ?_⟩
  · change v.regValue .rsp = _
    rw [result.rsp]
    exact (callEffect_stack effect).2.trans frame.rsp
  · have h := pre.saved_word_preserved localFrame (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans frame.returnAddress
  · intro i hi
    exact (pre.saved_word_preserved localFrame (offset := 8*(i+1)) (by omega)).trans (frame.saved i hi)

theorem Pre.scratch_input_byte (pre : Pre s boundary)
    (frame : MemoryWriteFrame t u #v[scratchRegion s]) {i : Nat} (hi : i < 32) :
    u.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      t.external[s.regValue .rdi + BitVec.ofNat 64 i]? := by
  apply frame
  intro r hr ha
  have he : r = scratchRegion s := by simpa using hr
  subst r
  exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _
    (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
    (pre.scratch_subset ha)

theorem Pre.scratch_output_word (pre : Pre s boundary)
    (frame : MemoryWriteFrame t u #v[scratchRegion s]) {j : Nat} (hj : j < 4) :
    memLoad u.external (s.regValue .rdx + BitVec.ofNat 64 (8*j)) 64 =
      memLoad t.external (s.regValue .rdx + BitVec.ofNat 64 (8*j)) 64 := by
  apply memLoad_congr
  intro i hi
  change u.external[s.regValue .rdx + BitVec.ofNat 64 (8*j) + BitVec.ofNat 64 i]?.getD 0 =
    t.external[s.regValue .rdx + BitVec.ofNat 64 (8*j) + BitVec.ofNat 64 i]?.getD 0
  congr 1
  apply frame
  intro r hr ha
  have he : r = scratchRegion s := by simpa using hr
  subst r
  apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ ?_ (pre.scratch_subset ha)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact pre.output_contains (by omega)

end P256.Proofs.ReadBe
