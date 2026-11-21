import P256.Proofs.Program.Interface
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.State
import P256.Proofs.Field.Representation
import P256.Proofs.Program.Stack
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}

theorem after_registers {components : List Component} {fuel : Nat}
    (pre : Pre initial boundary) (stage : Stage initial s boundary)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (memory : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (rsp : .reg 4 ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Stage initial t boundary := by
  apply stage.of_agrees pre run ready agrees
  · intro c hc a ha
    exact (memory c hc a ha).elim
  · intro c hc a _
    exact memory c hc a
  · exact rsp

theorem order_preserved (pre : Pre initial boundary)
    (stage : Stage initial s boundary) :
    Nat256At s (initial.regValue .rsi) P256.Spec.Operations.domain.n := by
  refine ⟨pre.order.1, ?_⟩
  intro i hi
  rw [stage.frame]
  · exact pre.order.2 i hi
  · intro region hr ha
    have inside := memoryRegion_contains_add pre.orderBounded
      (Nat.le_refl _) (Nat.le_refl _) hi
    have cases : region = registerRegion initial .rdx 32 ∨ region = Stack.region initial 128 := by
      simpa using hr
    rcases cases with rfl | rfl
    · exact pre.orderOutput _ inside ha
    · exact pre.orderStack _ inside ha

theorem order_readable (pre : Pre initial boundary)
    (stage : Stage initial s boundary) (offset : Nat) (bound : offset + 8 ≤ 32) :
    MemReadable s (initial.regValue .rsi + BitVec.ofNat 64 offset) 8 := by
  apply readable_of_grow _ stage.allocated
  have low : (initial.regValue .rsi).toNat + offset < 2^64 := by
    have h := pre.orderBounded
    change (initial.regValue .rsi).toNat + 32 < 2^32 at h
    omega
  have addr : (initial.regValue .rsi + BitVec.ofNat 64 offset).toNat =
      (initial.regValue .rsi).toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show offset < 2^64 by omega), Nat.mod_eq_of_lt low]
  apply memoryRegion_memReadable pre.orderBounded pre.orderAllocated
  · change (initial.regValue .rsi).toNat ≤ _
    rw [addr]
    omega
  · change _ ≤ (initial.regValue .rsi).toNat + 32
    rw [addr]
    omega

theorem scratch_address (stage : Stage initial s boundary) :
    stackPtr s + 15 = stackPtr initial - 57 := by
  rw [stage.rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]

theorem scratch_readable (pre : Pre initial boundary)
    (stage : Stage initial s boundary) :
    MemReadable s (stackPtr s + 15) 1 := by
  rw [scratch_address stage]
  exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide))
    stage.allocated

theorem scratch_writable (pre : Pre initial boundary)
    (stage : Stage initial s boundary) :
    MemWritable s (stackPtr s + 15) 1 := by
  rw [scratch_address stage]
  apply writable_of_grow _ stage.allocated
  apply stack_sub_writable pre.stack (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht)) (by decide) (by decide) (by decide)
  have := Nat.mod_lt (stackPtr initial - 57).toNat (by decide : 0 < 4096)
  omega

theorem scratch_code_apart (pre : Pre initial boundary)
    (stage : Stage initial s boundary) {offset len : Nat}
    (bound : offset + len ≤ 118431) :
    RangeApart (stackPtr s + 15) 1 (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  rw [scratch_address stage]
  intro i hi j hj eqn
  have inside := stackRegion_contains_sub pre.stack.2.2.1 (by decide : 57 ≤ 128)
    (by decide : 1 ≤ 57) ⟨i, hi, rfl⟩
  apply pre.avoids _ (by simp) _ inside
  apply Or.inl
  apply (congrArg InProgram eqn).mpr
  have addr : Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 j =
      Extracted.textAddress + BitVec.ofNat 64 (offset + j) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [addr]
  exact inProgram_of_textOffset (offset + j) (by omega)

theorem after_scratch {fuel : Nat} (pre : Pre initial boundary)
    (stage : Stage initial s boundary) (run : Advances boundary fuel s t)
    (ready : ReadyToStep t)
    (agrees : AgreesExcept [.mem (stackPtr initial - 57) 1, .rip] s t) :
    Stage initial t boundary := by
  apply stage.of_agrees pre run ready agrees
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨Stack.region initial 128, by simp,
        stackRegion_contains_sub pre.stack.2.2.1 (by decide) (by decide) ha⟩
    · exact ha.elim
  · intro c hc a saved written
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have apart : RangeApart (stackPtr initial - 57) 1 (stackPtr initial - 48) 56 := by
        have bounds := stack_bounds pre.stack
        apply RangeApart.of_toNat
        · rw [show (stackPtr initial - 57).toNat = (stackPtr initial).toNat - 57 from
            stack_sub_toNat pre.stack (by decide)]
          omega
        · rw [show (stackPtr initial - 48).toNat = (stackPtr initial).toNat - 48 from
            stack_sub_toNat pre.stack (by decide)]
          omega
        · rw [show (stackPtr initial - 57).toNat = (stackPtr initial).toNat - 57 from
            stack_sub_toNat pre.stack (by decide),
            show (stackPtr initial - 48).toNat = (stackPtr initial).toNat - 48 from
            stack_sub_toNat pre.stack (by decide)]
          omega
      obtain ⟨i, hi, eqi⟩ := written
      obtain ⟨j, hj, eqj⟩ := saved
      exact apart i hi j hj (eqi.symm.trans eqj)
    · exact written.elim
  · simp

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix
