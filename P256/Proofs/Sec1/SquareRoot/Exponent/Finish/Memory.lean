import P256.Proofs.Sec1.SquareRoot.Exponent.Preservation
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.CrossPageStore.Mov

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot.ExponentTail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

def components (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .flags, .rip, .mem (s.regValue .rdi) 32]

theorem output_contains (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    {i : Nat} (hi : i < 32) :
    (registerRegion s .rdi 32).Contains (s.regValue .rdi + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem memory (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (h : AgreesExcept (components s) t u) {a : BitVec 64}
    (ha : ¬ (registerRegion s .rdi 32).Contains a.toNat) :
    u.external[a]? = t.external[a]? := by
  apply h.byte
  intro c hc hv
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hv.elim
  obtain ⟨i, hi, rfl⟩ := hv
  exact ha (output_contains pre hi)

theorem loaded (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (h : AgreesExcept (components s) t u) (hl : ProgramLoaded t) : ProgramLoaded u := by
  intro a b hb
  rw [memory pre h]
  · exact hl a b hb
  · intro ha
    exact pre.avoids _ (by simp) a ha (.inl ⟨b, hb⟩)

theorem stack_memory (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (h : AgreesExcept (components s) t u) {off i : Nat} (ho : off ≤ 1584)
    (hi : i < off + 8) :
    u.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? := by
  apply memory pre h
  intro ha
  apply pre.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) _ ha
  apply memoryRegion_contains_add pre.stack.1 (len := off + 8) _ _ hi
  · rw [stack_sub_toNat pre.stack ho]
    exact Nat.sub_le_sub_left ho _
  · rw [stack_region_end, stack_sub_toNat pre.stack ho]
    have := (stack_bounds pre.stack).1
    omega

theorem stack_word (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (h : AgreesExcept (components s) t u) {off : Nat} (ho : off ≤ 1584) :
    (Operand.mem (stackPtr s - BitVec.ofNat 64 off) : Operand 64).read u =
      (Operand.mem (stackPtr s - BitVec.ofNat 64 off) : Operand 64).read t := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun b : Option UInt8 => b.getD 0) (stack_memory pre h ho (by omega))

theorem frame (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (hf : ExponentFrame s t) (hr : ReadyToStep u)
    (h : AgreesExcept (components s) t u) : ExponentFrame s u := by
  refine ⟨(h.read (n := 64) (r := 4) (by simp [components])).trans hf.rsp,
    supportedMachine_of_ready_agrees hf.machine hr h,
    bindingsSupported_of_ready_agrees hf.bindingsSupported hr h,
    h.directionFlagClear (by component_not_mem) hf.directionFlag,
    (h.mxcsr (by component_not_mem)).trans hf.mxcsr,
    (h.fcw (by component_not_mem)).trans hf.fp87, ?_, loaded pre h hf.loaded,
    fun a ha => h.grow a (hf.allocated a ha), ?_, ?_, ?_⟩
  · intro a ha
    rw [memory pre h (ha _ (by simp))]
    exact hf.frame a ha
  · have hw := stack_word pre h (off := 0) (by decide)
    simp only [BitVec.sub_zero] at hw
    exact hw.trans hf.returnAddress
  · intro i hi
    exact (stack_word pre h (off := 8 * (i + 1)) (by omega)).trans (hf.saved i hi)
  · have he : exponentFrameBase s + 0x2a0 = stackPtr s - 744 := by
      simp only [exponentFrameBase, stackPtr,
        BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    change (Operand.mem (exponentFrameBase s + 0x2a0) : Operand 64).read u = _
    have hw := stack_word pre h (off := 744) (by decide)
    change (Operand.mem (stackPtr s - 744) : Operand 64).read u =
      (Operand.mem (stackPtr s - 744) : Operand 64).read t at hw
    rw [← he] at hw
    exact hw.trans hf.outputPointer

theorem output_readable (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (hf : ExponentFrame s t) {off len : Nat} (hn : off + len ≤ 32) :
    MemReadable t (s.regValue .rdi + BitVec.ofNat 64 off) len := by
  have hb : (s.regValue .rdi).toNat + 32 < 2^32 := pre.outputBounded
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2^64),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hf.allocated _ (Option.isSome_iff_exists.mpr (pre.outputAllocated _
      (output_contains pre (by omega))))

theorem output_writable (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (hf : ExponentFrame s t) {off len : Nat} (hn : off + len ≤ 32) (hl : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi + BitVec.ofNat 64 off) len := by
  refine ⟨output_readable pre hf hn, tables_of_not_reserved hl (output_readable pre hf hn).low ?_⟩
  intro i hi hin
  apply pre.avoids (registerRegion s .rdi 32) (by simp) _ _ (.inr hin)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact output_contains pre (by omega)

theorem output_code (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    {off len pc n : Nat} (hn : off + len ≤ 32) (hp : pc + n ≤ 118431) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 off) len
      (Extracted.textAddress + BitVec.ofNat 64 pc) n := by
  intro i hi j hj he
  apply pre.avoids (registerRegion s .rdi 32) (by simp)
    (s.regValue .rdi + BitVec.ofNat 64 off + BitVec.ofNat 64 i) _ (.inl ?_)
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact output_contains pre (by omega)
  · rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (pc+j) (by omega)

omit [Bindings] in
theorem widen_output {cs : List Component} {off len : Nat}
    (h : AgreesExcept (cs ++ [.mem (s.regValue .rdi + BitVec.ofNat 64 off) len]) t u)
    (hc : ∀ c ∈ cs, c ∈ components s) (hn : off + len ≤ 32) :
    AgreesExcept (components s) t u := by
  apply h.widen
  · intro c hm hnmem
    rcases List.mem_append.mp hm with hm | hm
    · exact hc c hm
    · simp only [List.mem_singleton] at hm
      subst c
      contradiction
  · intro a c hm hv
    rcases List.mem_append.mp hm with hm | hm
    · exact ⟨c, hc c hm, hv⟩
    · simp only [List.mem_singleton] at hm
      subst c
      obtain ⟨i, hi, rfl⟩ := hv
      exact ⟨.mem (s.regValue .rdi) 32, by simp [components], off+i, by omega,
        by rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩

omit [Bindings] in
theorem word_of_registers {cs : List Component} {a v : BitVec 64}
    (h : AgreesExcept cs t u) (hc : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (hw : exponentWordAt t a v) : exponentWordAt u a v :=
  exponentWordAt_of_memory (fun a => congrArg (fun m : Ram => m[a]?) (h.external hc)) hw

theorem word_of_store (_pre : CalleePre s boundary 0x114ba0 144 32 1584)
    {off storeOff len : Nat} (ho : off + 8 ≤ 32) (hs : storeOff + len ≤ 32)
    (hap : off + 8 ≤ storeOff ∨ storeOff + len ≤ off) {v : BitVec 64}
    (h : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 storeOff) len, .rip] t u)
    (hw : exponentWordAt t (s.regValue .rdi + BitVec.ofNat 64 off) v) :
    exponentWordAt u (s.regValue .rdi + BitVec.ofNat 64 off) v := by
  apply Eq.trans _ hw
  apply memLoad_congr
  intro i hi
  apply congrArg (fun b : Option UInt8 => b.getD 0)
  apply h.byte
  intro c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := hv
    exact (RangeApart.offsets (s.regValue .rdi) (by omega) (by omega) hap) i hi j hj he
  · exact hv.elim

omit [Bindings] in
theorem frame_address {s : RamState} {off : Nat} (ho : off ≤ 1416) :
    exponentFrameBase s + BitVec.ofNat 64 off = stackPtr s - BitVec.ofNat 64 (1416 - off) := by
  change (stackPtr s - BitVec.ofNat 64 1416) + BitVec.ofNat 64 off = _
  rw [← BitVec.ofNat_sub_ofNat_of_le 1416 off (by omega) ho]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

theorem frame_readable (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (hf : ExponentFrame s t) {off : Nat} (ho : off ≤ 1416) :
    MemReadable t (exponentFrameBase s + BitVec.ofNat 64 off) 8 := by
  rw [frame_address ho]
  exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) hf.allocated

theorem frame_word (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (h : AgreesExcept (components s) t u) {off : Nat} (ho : off ≤ 1416) :
    (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 off) : Operand 64).read u =
      (Operand.mem (exponentFrameBase s + BitVec.ofNat 64 off) : Operand 64).read t := by
  rw [frame_address ho]
  exact stack_word pre h (by omega)

end P256.Proofs.Sec1.SquareRoot.ExponentTail
