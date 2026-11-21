import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Code
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Arithmetic
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Instructions.CrossPageStore.Mov

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

export P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction
  (modulus borrow subWord subRaw selectWord selectLimbs selector reduce
    subWord_toNat borrow_toNat subWord_borrow subWord_zero subRaw_toNat
    modulus_toNat selectWord_zero selectWord_one selectLimbs_zero selectLimbs_one
    selector_zero selector_one reduce_toNat selector_byte)

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure MemoryPre (s : RamState) : Prop where
  scratch : ∀ offset len : Nat, offset + len ≤ 112 → offset % 8 = 0 → len ≤ 8 →
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) len
  output : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (s.regValue .rdi) 32
  scratchCode : ∀ a, (Component.mem (stackPtr s) 112).Covers a → ¬ InProgram a
  outputCode : ∀ a, (Component.mem (s.regValue .rdi) 32).Covers a → ¬ InProgram a

def scratchComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15,
    .flags, .rip, .mem (stackPtr s) 112]

def components (s : RamState) : List Component :=
  scratchComponents s ++ [.mem (s.regValue .rdi) 32]

structure Input (s : RamState) (a : Limbs) (high : BitVec 64) : Prop where
  l0 : (Operand.reg 1 : Operand 64).read s = a.l0
  l1 : (Operand.reg 6 : Operand 64).read s = a.l1
  l2 : (Operand.reg 0 : Operand 64).read s = a.l2
  l3 : (Operand.reg 2 : Operand 64).read s = a.l3
  hi : (Operand.reg 15 : Operand 64).read s = high

structure Modulus (s : RamState) (p : Limbs) : Prop where
  l0 : (Operand.mem (stackPtr s + 0x20) : Operand 64).read s = p.l0
  l1 : (Operand.mem (stackPtr s + 0x30) : Operand 64).read s = p.l1
  l2 : (Operand.mem (stackPtr s + 0x28) : Operand 64).read s = p.l2
  l3 : (Operand.reg 12 : Operand 64).read s = p.l3

structure Difference (s : RamState) (r : Limbs) (b : BitVec 64) : Prop where
  l0 : (Operand.reg 8 : Operand 64).read s = r.l0
  l1 : (Operand.reg 9 : Operand 64).read s = r.l1
  l2 : (Operand.reg 11 : Operand 64).read s = r.l2
  l3 : (Operand.reg 14 : Operand 64).read s = r.l3
  negBorrow : (Operand.reg 13 : Operand 64).read s = -b

theorem MemoryPre.of_grow {s t : RamState} (h : MemoryPre s)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rsp : stackPtr t = stackPtr s) (rdi : t.regValue .rdi = s.regValue .rdi) :
    MemoryPre t := by
  constructor
  · intro offset len hbound halign hlen
    rw [rsp]
    have hw := h.scratch offset len hbound halign hlen
    exact ⟨hw.low, fun i hi => grow _ (hw.mem i hi), hw.tables⟩
  · rw [rdi]
    exact ⟨⟨h.output.low, fun i hi => grow _ (h.output.mem i hi)⟩, h.output.tables⟩
  · rw [rsp]
    exact h.scratchCode
  · rw [rdi]
    exact h.outputCode

theorem scratch_covered {s : RamState} {offset len : Nat} (h : offset + len ≤ 112)
    {a : BitVec 64} (ha : (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a) :
    (Component.mem (stackPtr s) 112).Covers a := by
  obtain ⟨i, hi, rfl⟩ := ha
  exact ⟨offset+i, by omega, by rw [BitVec.add_assoc, BitVec.ofNat_add]⟩

theorem output_covered {s : RamState} {offset len : Nat} (h : offset + len ≤ 32)
    {a : BitVec 64} (ha : (Component.mem (s.regValue .rdi + BitVec.ofNat 64 offset) len).Covers a) :
    (Component.mem (s.regValue .rdi) 32).Covers a := by
  obtain ⟨i, hi, rfl⟩ := ha
  exact ⟨offset+i, by omega, by rw [BitVec.add_assoc, BitVec.ofNat_add]⟩

theorem scratch_rsp {s t : RamState} (h : AgreesExcept (scratchComponents s) s t) :
    stackPtr t = stackPtr s := by
  exact h.read (r := 4) (n := 64) (by simp [scratchComponents])

theorem scratch_rdi {s t : RamState} (h : AgreesExcept (scratchComponents s) s t) :
    t.regValue .rdi = s.regValue .rdi := by
  exact h.read (r := 7) (n := 64) (by simp [scratchComponents])

theorem components_rsp {s t : RamState} (h : AgreesExcept (components s) s t) :
    stackPtr t = stackPtr s := by
  exact h.read (r := 4) (n := 64) (by simp [components, scratchComponents])

theorem components_rdi {s t : RamState} (h : AgreesExcept (components s) s t) :
    t.regValue .rdi = s.regValue .rdi := by
  exact h.read (r := 7) (n := 64) (by simp [components, scratchComponents])

theorem MemoryPre.of_scratch {s t : RamState} (h : MemoryPre s)
    (ag : AgreesExcept (scratchComponents s) s t) : MemoryPre t :=
  h.of_grow ag.grow (scratch_rsp ag) (scratch_rdi ag)

theorem MemoryPre.of_components {s t : RamState} (h : MemoryPre s)
    (ag : AgreesExcept (components s) s t) : MemoryPre t :=
  h.of_grow ag.grow (components_rsp ag) (components_rdi ag)

theorem MemoryPre.loaded {s t : RamState} (h : MemoryPre s)
    (ag : AgreesExcept (components s) s t) (loaded : ProgramLoaded s) : ProgramLoaded t := by
  intro a b hb
  rw [ag.memory a]
  · exact loaded a b hb
  · intro c hc hcov
    simp only [components, scratchComponents, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals first
      | exact hcov.elim
      | exact h.scratchCode a hcov ⟨b, hb⟩
      | exact h.outputCode a hcov ⟨b, hb⟩

theorem MemoryPre.scratch_apart {s : RamState} (h : MemoryPre s)
    {entry : BitVec 64} (he : Entry entry) (offset len codeOffset codeLen : Nat)
    (hs : offset + len ≤ 112) (hc : codeOffset + codeLen ≤ 1469) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (entry + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj hij
  apply h.scratchCode _ (scratch_covered hs ⟨i, hi, rfl⟩)
  rw [hij, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact instruction_in_program he (codeOffset+j) (by omega)

theorem MemoryPre.output_apart {s : RamState} (h : MemoryPre s)
    {entry : BitVec 64} (he : Entry entry) (offset len codeOffset codeLen : Nat)
    (hs : offset + len ≤ 32) (hc : codeOffset + codeLen ≤ 1469) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 offset) len
      (entry + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj hij
  apply h.outputCode _ (output_covered hs ⟨i, hi, rfl⟩)
  rw [hij, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact instruction_in_program he (codeOffset+j) (by omega)

theorem scratch_then_components {s t u : RamState}
    (h₁ : AgreesExcept (scratchComponents s) s t)
    (h₂ : AgreesExcept (components t) t u) : AgreesExcept (components s) s u := by
  have he : components t = components s := by
    simp only [components, scratchComponents, scratch_rsp h₁, scratch_rdi h₁]
  rw [he] at h₂
  apply (h₁.trans h₂).mono
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact List.mem_append_left _ h
  · exact h

theorem scratch_trans {s t u : RamState}
    (h₁ : AgreesExcept (scratchComponents s) s t)
    (h₂ : AgreesExcept (scratchComponents t) t u) :
    AgreesExcept (scratchComponents s) s u := by
  have he : scratchComponents t = scratchComponents s := by
    simp only [scratchComponents, scratch_rsp h₁]
  rw [he] at h₂
  exact (h₁.trans h₂).mono (by simp)

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
