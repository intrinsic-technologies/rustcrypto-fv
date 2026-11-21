import Hkdf.Proofs.Standard.Finalize.Suffix.State
import Hkdf.Proofs.Standard.Finalize.Suffix.Return.Stores
import Hkdf.Proofs.Common.Refine
import Hkdf.Proofs.Common.Encoding.Serialize.Stack

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Return

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Machine

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}

theorem output_nat (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    {offset : Nat} (within : offset ≤ 176) :
    (initial.regValue .rdi + BitVec.ofNat 64 offset).toNat =
      (initial.regValue .rdi).toNat + offset := by
  exact toNat_add_ofNat _ _ (by have h : (initial.regValue .rdi).toNat + 176 < 2^32 := pre.outputBounded; omega)

theorem output_contains (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    {offset : Nat} (within : offset < 176) :
    (registerRegion initial .rdi 176).Contains
      (initial.regValue .rdi + BitVec.ofNat 64 offset).toNat := by
  rw [output_nat pre (by omega)]
  change (initial.regValue .rdi).toNat ≤ (initial.regValue .rdi).toNat + offset ∧
    (initial.regValue .rdi).toNat + offset < (initial.regValue .rdi).toNat + 176
  constructor <;> omega

theorem output_writable (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : State initial boundary s) :
    Hkdf.Proofs.Refine.Writable Extracted.programImage s.external (initial.regValue .rdi) 176 := by
  have low : (initial.regValue .rdi).toNat + 176 ≤ 2^32 := Nat.le_of_lt pre.outputBounded
  refine ⟨⟨low, ?_⟩, tables_of_not_reserved (by decide) low ?_, ?_⟩
  · intro i hi
    exact state.running.allocated _ (Option.isSome_iff_exists.mpr
      (pre.outputAllocated _ (output_contains pre hi)))
  · intro i hi reserved
    exact pre.avoids _ (by simp) _ (output_contains pre hi) (.inr reserved)
  · intro x code i hi equal
    exact pre.avoids _ (by simp) _ (output_contains pre hi) (.inl ⟨x.2, equal ▸ code⟩)

theorem output_apart_stack (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    {offset len stackOffset stackLen : Nat}
    (outputWithin : offset + len ≤ 176) (stackWithin : stackOffset ≤ 1264)
    (stackHigh : stackLen ≤ stackOffset + 8) :
    RangeApart (initial.regValue .rdi + BitVec.ofNat 64 offset) len
      (stackPtr initial - BitVec.ofNat 64 stackOffset) stackLen := by
  intro i hi j hj equal
  have output := output_contains pre (offset := offset + i) (by omega)
  have stack : (Stack.region initial 1264).Contains
      (stackPtr initial - BitVec.ofNat 64 stackOffset + BitVec.ofNat 64 j).toNat :=
    Hkdf.Proofs.Common.Machine.memoryRegion_contains_add pre.stack.1
      (by rw [Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_toNat pre stackWithin];
          change (stackPtr initial).toNat - 1264 ≤ _; omega)
      (by rw [Hkdf.Proofs.Common.Machine.stack_region_end,
          Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_toNat pre stackWithin];
          have h : 1264 ≤ (stackPtr initial).toNat := pre.stack.2.2.1; omega) hj
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, equal] at output
  exact pre.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) _ output stack

theorem output_code_apart (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    {offset len pc codeLen : Nat} (within : offset + len ≤ 176)
    (pcLow : 0x10e240 ≤ pc) (pcHigh : pc + codeLen ≤ 0x10e273) :
    RangeApart (initial.regValue .rdi + BitVec.ofNat 64 offset) len
      (BitVec.ofNat 64 pc) codeLen := by
  intro i hi j hj equal
  have inside := inProgram_of_textOffset (pc - 0x100000 + j) (by omega)
  have addr : (BitVec.ofNat 64 (0x100000 + (pc - 0x100000 + j))) =
      BitVec.ofNat 64 pc + BitVec.ofNat 64 j := by
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  have combine : Extracted.textAddress + BitVec.ofNat 64 (pc - 0x100000 + j) =
      BitVec.ofNat 64 (0x100000 + (pc - 0x100000 + j)) :=
    (BitVec.ofNat_add (n := 64) 0x100000 (pc - 0x100000 + j)).symm
  have inside' : InProgram (BitVec.ofNat 64 (0x100000 + (pc - 0x100000 + j))) := combine ▸ inside
  rw [addr, ← equal] at inside'
  apply pre.avoids (registerRegion initial .rdi 176) (by simp) _ _ (.inl inside')
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
    output_contains pre (offset := offset + i) (by omega)

theorem stores_pre (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : State initial boundary s) (rip : s.RIP = 0x10e240) : Stores.Pre s := by
  have writable := output_writable pre state
  have sub (offset length : Nat) (within : offset + length ≤ 176) :
      Hkdf.Proofs.Refine.Writable Extracted.programImage s.external
        (initial.regValue .rdi + BitVec.ofNat 64 offset) length := by
    apply writable.sub <;> rw [output_nat pre (by omega)] <;> omega
  refine ⟨rip, ?_, ?_, ?_, ?_, ?_⟩
  · intro i member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    change MemReadable s (stackPtr s + i) 8
    rw [state.rsp]
    rcases member with rfl | rfl | rfl | rfl
    · have h := Hkdf.Proofs.Common.Encoding.Serialize.readable_of_grow
        (Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_readable pre (offset := 192)
          (by decide) (by decide : 8 ≤ 192 + 8)) state.running.allocated
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
    · have h := Hkdf.Proofs.Common.Encoding.Serialize.readable_of_grow
        (Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_readable pre (offset := 184)
          (by decide) (by decide : 8 ≤ 184 + 8)) state.running.allocated
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
    · have h := Hkdf.Proofs.Common.Encoding.Serialize.readable_of_grow
        (Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_readable pre (offset := 176)
          (by decide) (by decide : 8 ≤ 176 + 8)) state.running.allocated
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
    · have h := Hkdf.Proofs.Common.Encoding.Serialize.readable_of_grow
        (Hkdf.Proofs.Common.Encoding.Serialize.stack_sub_readable pre (offset := 168)
          (by decide) (by decide : 8 ≤ 168 + 8)) state.running.allocated
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using h
  · intro i member
    change Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s (s.regValue .rbx + i) 8
    rw [state.rbx]
    have hi : i.toNat + 8 ≤ 176 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    have h := sub i.toNat 8 hi
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      (show Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s
        (initial.regValue .rdi + BitVec.ofNat 64 i.toNat) 8 from
        ⟨⟨h.readable.low, h.readable.present⟩, h.tables⟩)
  · change MemWritable s (s.regValue .rbx + 95) 1
    rw [state.rbx]
    have h := sub 95 1 (by decide)
    exact ⟨h.readable.low, h.readable.present, h.tables⟩
  · intro i member pc codeLen low high
    change RangeApart (s.regValue .rbx + i) (if i = 95 then 1 else 8) (BitVec.ofNat 64 pc) codeLen
    rw [state.rbx]
    have hi : i.toNat + (if i = 95 then 1 else 8) ≤ 176 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      output_code_apart pre hi low high
  · intro i member j jm
    change RangeApart (s.regValue .rbx + i) 8 (stackPtr s + j) 8
    rw [state.rbx, state.rsp]
    have hi : i.toNat + 8 ≤ 176 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    have jb : j.toNat ≤ 408 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at jm
      rcases jm with rfl | rfl | rfl | rfl <;> decide
    have addr : stackPtr initial - 408 + j =
        stackPtr initial - BitVec.ofNat 64 (408 - j.toNat) := by
      rw [← BitVec.ofNat_sub_ofNat_of_le (w := 64) 408 j.toNat (by omega) jb,
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, ← addr] using
      output_apart_stack pre hi (stackOffset := 408 - j.toNat)
        (stackLen := 8) (by omega) (by omega)

end Hkdf.Proofs.Standard.Finalize.Suffix.Return
