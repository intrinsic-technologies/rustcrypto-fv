import P256.Proofs.Field.Schoolbook.Execution
import P256.Proofs.Field.Schoolbook.LowerSums

set_option autoImplicit false

open P256.Proofs.Common.Field.SquareRoot.Multiply (prologueComponents)
open P256.Proofs.Program (inProgram_of_textOffset memoryRegion_memReadable)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec.Program.Routines

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s entry t : RamState} {boundary : ReturnBoundary}
  {ctx : ExecutionContext s boundary entry}

omit [Bindings] in
theorem products_savedSource (h : (productsEffect entry).Holds entry t) :
    savedSource t = (Operand.reg 6 : Operand 64).read entry := by
  have hsp : rspOf t = rspOf entry := h.agrees.read (by simp [productsEffect, Effect.components])
  simp only [savedSource, hsp]
  exact h.writes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem lower_pre (state : BodyState ctx t) (hp : (productsEffect entry).Holds entry t) :
    LowerSumsPre 0x11c9f6 122 t := by
  have src : savedSource t = s.regValue .rsi := (products_savedSource hp).trans
    (ctx.agrees.read (by simp [prologueComponents]))
  refine ⟨state.scratchPre hp.rip ?_, ?_, ?_⟩
  · intro j hj
    change InProgram ((Extracted.textAddress+BitVec.ofNat 64 0x1c9f6)+BitVec.ofNat 64 j)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (0x1c9f6+j) (by omega)
  · rw [src]
    exact products_readable_slice (readable_of_grow
      (memoryRegion_memReadable ctx.pre.inputBounded ctx.pre.inputAllocated
        (Nat.le_refl _) (Nat.le_refl _)) state.grow) 24 (by decide)
  · rw [src]
    have apart := scratch_apart_region ctx.pre state.rsp ctx.pre.inputBounded
      (ctx.pre.separation (0 : Fin 3) 2 (by decide))
    intro i hi j hj
    have he := apart i hi (24+j) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

theorem upper_products_pre (state : BodyState ctx t) (rip : t.RIP = 0x11ca70)
    (source : t.regValue .rsi = s.regValue .rsi) : UpperProductsPre t := by
  refine ⟨state.scratchPre rip ?_, ?_, ?_⟩
  · intro j hj
    change InProgram ((Extracted.textAddress+BitVec.ofNat 64 0x1ca70)+BitVec.ofNat 64 j)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (0x1ca70+j) (by omega)
  · change MemReadable t (t.regValue .rsi+16) 8
    rw [source]
    exact products_readable_slice (readable_of_grow
      (memoryRegion_memReadable ctx.pre.inputBounded ctx.pre.inputAllocated
        (Nat.le_refl _) (Nat.le_refl _)) state.grow) 16 (by decide)
  · intro c hc
    change RangeApart (rspOf t+c) 8 (t.regValue .rsi+16) 8
    rw [source]
    have apart := scratch_apart_region ctx.pre state.rsp ctx.pre.inputBounded
      (ctx.pre.separation (0 : Fin 3) 2 (by decide))
    apply products_apart_slice apart
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> decide
    · decide

end P256.Proofs.Field.Schoolbook
