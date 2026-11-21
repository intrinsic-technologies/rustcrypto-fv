import P256.Proofs.ReadBe.State
import P256.Proofs.Program.Stack
import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem Pre.stack_avoids_tables (pre : Pre s boundary) :
    (Stack.region s 128).Avoids InPageTables :=
  fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)

theorem Pre.stack_contains (pre : Pre s boundary) {offset len i : Nat}
    (hoffset : offset ≤ 128) (hlen : len ≤ offset + 8) (hi : i < len) :
    (Stack.region s 128).Contains
      (stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
  apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [stack_sub_toNat pre.stack hoffset]
    change (stackPtr s).toNat - 128 ≤ (stackPtr s).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack hoffset]
    have := (stack_bounds pre.stack)
    omega

theorem Pre.stack_code_apart (pre : Pre s boundary) {offset len codeOffset codeLen : Nat}
    (hoffset : offset ≤ 128) (hlen : len ≤ offset + 8)
    (hcode : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr s - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj he
  apply pre.avoids (Stack.region s 128) (by simp) _ (pre.stack_contains hoffset hlen hi)
  left
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset _ (by omega)

theorem Pre.output_readable (pre : Pre s boundary) {offset len : Nat}
    (hlen : offset + len ≤ 32) :
    MemReadable s (s.regValue .rdx + BitVec.ofNat 64 offset) len := by
  apply memoryRegion_memReadable pre.outputBounded pre.outputAllocated
  · change (s.regValue .rdx).toNat ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by have := pre.outputBounded; change (s.regValue .rdx).toNat + 32 < 2^32 at this; omega)]
    omega
  · change _ + len ≤ (s.regValue .rdx).toNat + 32
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by have := pre.outputBounded; change (s.regValue .rdx).toNat + 32 < 2^32 at this; omega)]
    omega

theorem Pre.output_contains (pre : Pre s boundary) {i : Nat} (hi : i < 32) :
    (registerRegion s .rdx 32).Contains (s.regValue .rdx + BitVec.ofNat 64 i).toNat :=
  memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi

theorem Pre.output_writable (pre : Pre s boundary) {offset len : Nat}
    (hlen : offset + len ≤ 32) (hpos : 0 < len) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (s.regValue .rdx + BitVec.ofNat 64 offset) len := by
  have read := pre.output_readable hlen
  refine ⟨read, tables_of_not_reserved hpos read.low ?_⟩
  intro i hi reserved
  apply pre.avoids (registerRegion s .rdx 32) (by simp) _ ?_ (.inr reserved)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact pre.output_contains (by omega)

theorem Pre.input_preserved (pre : Pre s boundary)
    (frame : MemoryWriteFrame s t #v[registerRegion s .rdx 32, Stack.region s 128])
    {i : Nat} (hi : i < 32) :
    t.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rdi + BitVec.ofNat 64 i]? := by
  apply frame
  intro region hr
  have hin := memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : region = registerRegion s .rdx 32 ∨ region = Stack.region s 128 := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ hin
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hin

end P256.Proofs.ReadBe
