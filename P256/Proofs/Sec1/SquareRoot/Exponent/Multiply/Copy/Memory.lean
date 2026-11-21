import P256.Proofs.Sec1.SquareRoot.Exponent.Multiply.State
import P256.Proofs.Sec1.SquareRoot.Exponent.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentMultiply.Copy

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem word_of_registers {t u : RamState} {cs : List Component} {address : BitVec 64}
    (h : AgreesExcept cs t u) (hm : ∀ c ∈ cs, ∀ a, ¬ c.Covers a := by simp [Component.Covers]) :
    (Operand.mem address : Operand 64).read u = (Operand.mem address : Operand 64).read t := by
  change memLoad u.external _ 64 = memLoad t.external _ 64
  rw [h.external hm]

theorem word_of_store_apart {t u : RamState} {base a b : BitVec 64}
    (h : AgreesExcept [.mem (base + a) 8, .rip] t u) (apart : OffsetsApart a 8 b 8) :
    (Operand.mem (base + b) : Operand 64).read u =
      (Operand.mem (base + b) : Operand 64).read t := by
  apply exponent_word_of_bytes
  intro i hi
  apply h.memory
  intro c hc cover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := cover
    exact apart.ne base hj hi (by decide +kernel) he.symm
  · exact cover

theorem bytes_of_store {s t u : RamState} {off offset len i : Nat}
    (ha : AgreesExcept [.mem (exponentFrameBase s + BitVec.ofNat 64 off) 8, .rip] t u)
    (hoff : off + 8 ≤ 80) (lo : 80 ≤ offset) (bound : offset + len ≤ 1368) (hi : i < len) :
    u.external[exponentFrameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[exponentFrameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply ha.memory
  intro c hc cover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := cover
    exact (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega)
      (.inl (by omega)) : RangeApart (exponentFrameBase s + BitVec.ofNat 64 off) 8
        (exponentFrameBase s + BitVec.ofNat 64 offset) len) j hj i hi he.symm
  · exact cover

theorem frame_of_store [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x off : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (ready : ReadyToStep u)
    (ha : AgreesExcept [.mem (exponentFrameBase s + BitVec.ofNat 64 off) 8, .rip] t u)
    (hoff : off + 8 ≤ 80) : ExponentFrame s u := by
  apply ExponentFrame.of_scalarFrame
  · apply hf.scalarFrame.after_effect ctx.toCalleePre (by decide) ready ha _ (by simp)
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨ScalarFrame.workRegion s 1584, by simp, ?_⟩
      have addr := ScalarFrame.scalar_stack_address (frameOffset := 1416) hf.scalarFrame.rsp
        (offset := off) (by decide) (by omega)
      change t.regValue .rsp + BitVec.ofNat 64 off = _ at addr
      rw [hf.rsp] at addr
      rw [addr] at cover
      exact ScalarFrame.work_contains ctx.toCalleePre (by omega) (by omega) cover
    · exact cover.elim
  · exact (exponent_word_of_bytes (n := 64) (fun i hi =>
      bytes_of_store (offset := 0x2a0) (len := 8) ha hoff (by decide) (by decide) hi)).trans
      hf.outputPointer

theorem position_of_store [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {x n off : Nat}
    (ctx : ExponentPre s boundary x) (h : ExponentPosition s t x n) (hf : ExponentFrame s u)
    (ha : AgreesExcept [.mem (exponentFrameBase s + BitVec.ofNat 64 off) 8, .rip] t u)
    (hoff : off + 8 ≤ 80) : ExponentPosition s u x n := by
  exact ⟨hf, h.constants.of_upper_bytes ctx hf (cutoff := 80) (by decide)
      (fun _ _ lo bound _ hi => bytes_of_store ha hoff lo bound hi),
    (ha.read (n := 64) (r := 5) (by simp)).trans h.word,
    (exponent_word_of_bytes (n := 64) (fun i hi =>
      bytes_of_store (offset := 0x2c0) (len := 8) ha hoff (by decide) (by decide) hi)).trans h.savedWord,
    (ha.read (n := 64) (r := 14) (by simp)).trans h.window,
    (ha.read (n := 64) (r := 3) (by simp)).trans h.firstWord,
    (ha.read (n := 64) (r := 13) (by simp)).trans h.firstWindow,
    (ha.read (n := 64) (r := 15) (by simp)).trans h.parameterPointer,
    (ha.read (n := 64) (r := 11) (by simp)).trans h.modulus0,
    (ha.read (n := 64) (r := 12) (by simp)).trans h.inverse⟩

end P256.Proofs.Sec1.SquareRoot.ExponentMultiply.Copy
