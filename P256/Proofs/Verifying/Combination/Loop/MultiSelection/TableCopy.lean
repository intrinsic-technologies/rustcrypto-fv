import P256.Proofs.Verifying.Combination.Loop.MultiSelection.State
import P256.Proofs.Verifying.Combination.PointMemory
import P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi.Selection

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem table_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitData s t tables digits p q u v k point left)
    (i : Fin 8) (offset destination : Nat) (hd : 144 ≤ destination) (hd' : destination ≤ 240)
    (bound : offset + 3 < 118431)
    (code : Extracted.textBytes.toListFrom offset 3 = [0xf3,0x48,0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (src : t.regValue .rsi = tables + (if left then 0 else 768) + BitVec.ofNat 64 (96*i.val))
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 destination)
    (count : t.regValue .rcx = 12) :
    ∃ w, Advances boundary 12 t w ∧ DigitData s w tables digits p q u v k point left ∧
      w.RIP = Extracted.textAddress + BitVec.ofNat 64 offset + (3 : BitVec 64) ∧
      ProjectiveAt w (stackPtr s - BitVec.ofNat 64 destination)
        (Table.oddTable (if left then p else q) i) ∧
      AgreesExcept (copyComponents s destination) t w := by
  let index : Nat := (if left then 0 else 768) + 96*i.val
  have hindex : index + 96 ≤ 1536 := by have := i.isLt; cases left <;> dsimp [index] <;> omega
  have source : t.regValue .rsi = tables + BitVec.ofNat 64 index := by
    rw [src]
    cases left <;> simp [index, BitVec.ofNat_add, BitVec.add_assoc]
  have tb : tables.toNat + 1536 < 2^32 := pre.tablesBounded
  have sn : (t.regValue .rsi).toNat = tables.toNat + index := by
    rw [source, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have readable : MemReadable t (t.regValue .rsi) 96 := by
    apply readable_of_grow (s := s) _ state.allocated
    apply memoryRegion_memReadable pre.tablesBounded pre.tablesAllocated
    · change tables.toNat ≤ _; rw [sn]; omega
    · change _ + 96 ≤ tables.toNat + 1536; rw [sn]; omega
  have apart : (t.regValue .rsi).toNat + 96 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 96 ≤ (t.regValue .rsi).toNat := by
    rw [sn, dst, stack_sub_toNat pre.stack (by omega)]
    have hs := stack_bounds pre.stack
    by_cases h : tables.toNat + index + 96 ≤ (stackPtr s).toNat - destination
    · exact Or.inl h
    · apply Or.inr
      apply Nat.le_of_not_gt
      intro hn
      apply pre.tablesStack (max (tables.toNat + index) ((stackPtr s).toNat - destination))
      · change tables.toNat ≤ _ ∧ _ < tables.toNat + 1536
        constructor <;> omega
      · change (stackPtr s).toNat - 1432 ≤ _ ∧
          _ < (stackPtr s).toNat - 1432 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 1432))
        constructor <;> omega
  have value : ProjectiveAt t (t.regValue .rsi) (Table.oddTable (if left then p else q) i) := by
    rw [src]
    cases left
    · exact state.rightTable i
    · simpa using state.leftTable i
  obtain ⟨w, run, frame, next, valueW, agrees, _⟩ := copy_to_stack (frameOffset := 408)
    pre.toCalleePre state.toFrameState offset bound code rip destination (by omega) hd
    dst count readable apart value (by decide)
  have kept (off len : Nat) (ho : off ≤ 1432) (hl : len ≤ off+8)
      (apart : off + 96 ≤ destination ∨ destination + len ≤ off) :
      ∀ j < len, w.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 j]? =
        t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 j]? := by
    intro j hj
    exact copy_byte pre.toCalleePre agrees (by omega) hd ho hl apart hj
  have slots (off : Nat) (ho : off ≤ 408) (ha : destination + 8 ≤ off) :
      memLoad w.external (stackPtr s - BitVec.ofNat 64 off) 64 =
        memLoad t.external (stackPtr s - BitVec.ofNat 64 off) 64 := by
    apply memLoad_congr
    intro j hj
    exact congrArg (fun x : Option UInt8 => x.getD 0)
      (kept off 8 (by omega) (by omega) (Or.inr ha) j hj)
  refine ⟨w, run, ⟨⟨state.toMemory.of_frame pre frame,
    (agrees.read (n := 64) (r := 3) (by simp [copyComponents])).trans state.count,
    state.positive, state.bounded,
    (agrees.read (n := 64) (r := 15) (by simp [copyComponents])).trans state.scratch,
    state.value.of_bytes_eq (kept 336 96 (by decide) (by decide) (by omega)), ?_, ?_, ?_⟩,
    (agrees.read (n := 64) (r := 13) (by simp [copyComponents])).trans state.cursor,
    (agrees.read (n := 64) (r := 5) (by simp [copyComponents])).trans state.tableCursor,
    (agrees.read (n := 64) (r := 12) (by simp [copyComponents])).trans state.remaining, ?_⟩,
    next, valueW, agrees⟩
  · exact (slots 400 (by decide) (by omega)).trans state.total
  · exact (slots 384 (by decide) (by omega)).trans state.tableBase
  · exact (slots 392 (by decide) (by omega)).trans state.output
  · exact (slots 376 (by decide) (by omega)).trans state.savedCursor

end P256.Proofs.Verifying.Combination.Loop.Multi.Selection
