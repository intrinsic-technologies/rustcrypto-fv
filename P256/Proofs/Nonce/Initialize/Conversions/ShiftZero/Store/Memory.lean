import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

structure OutputState (s t : RamState) (boundary : ReturnBoundary) (a : Limbs) : Prop
    extends Stage s t boundary where
  rip : t.RIP = 0x1096c5
  rax : t.regValue .rax = s.regValue .rdi
  r14 : t.regValue .r14 = a.l0
  rbx : t.regValue .rbx = a.l1
  r9 : t.regValue .r9 = a.l2
  r10 : t.regValue .r10 = a.l3

theorem byte_store_saved_pointer (stage : Stage s t boundary) {offset : Nat}
    (ho : offset < 16)
    (h : AgreesExcept [.mem (rspOf t + BitVec.ofNat 64 offset) 1, .rip] t u) :
    memLoad u.external (stackPtr s - 56) 64 = memLoad t.external (stackPtr s - 56) 64 := by
  have hp : rspOf t + 16 = stackPtr s - 56 := stage.scratch_address (offset := 16) (by decide)
  rw [← hp]
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h
  intro i hi c hc ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := ha
    have apart : OffsetsApart (BitVec.ofNat 64 offset) 1 16 8 := by
      unfold OffsetsApart
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]
      omega
    exact apart.ne (rspOf t) hj hi (by decide) he.symm
  · exact ha.elim

theorem output_writable (pre : CalleePre s boundary 0x109530 32 32 128)
    (stage : Stage s t boundary) {offset : Nat} (ho : offset + 8 ≤ 32) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t
      (s.regValue .rdi + BitVec.ofNat 64 offset) 8 := by
  have hr : MemReadable s (s.regValue .rdi) 32 :=
    memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _)
  have hs := P256.Proofs.Common.Memory.memReadable_sub hr offset 8 ho
  refine ⟨readable_of_grow hs stage.agrees.grow, ?_⟩
  apply tables_of_not_reserved (by decide) hs.low
  intro j hj hinside
  apply pre.avoids (registerRegion s .rdi 32) (by simp) _ _ (.inr hinside)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
    (show offset + j < 32 by omega)

theorem output_code_apart (pre : CalleePre s boundary 0x109530 32 32 128)
    {offset pc len : Nat} (ho : offset + 8 ≤ 32) (hc : pc + len ≤ 118431) :
    RangeApart (s.regValue .rdi + BitVec.ofNat 64 offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 pc) len := by
  intro i hi j hj he
  apply pre.avoids (registerRegion s .rdi 32) (by simp)
    (s.regValue .rdi + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) _ (.inl ?_)
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
      (show offset + i < 32 by omega)
  · rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (pc+j) (by omega)

theorem output_stage (pre : CalleePre s boundary 0x109530 32 32 128)
    (stage : Stage s t boundary) {fuel offset : Nat} (ho : offset + 8 ≤ 32)
    (run : Advances boundary fuel t u) (ready : ReadyToStep u)
    (h : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 offset) 8, .rip] t u) :
    Stage s u boundary := by
  have small : AgreesExcept (frame s) t u := by
    apply agrees_of_footprint h
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · contradiction
      · simp [frame]
    · intro c hc address ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨i, hi, rfl⟩ := ha
        refine ⟨.mem (s.regValue .rdi) 32, by simp [frame], offset+i, by omega, ?_⟩
        rw [BitVec.ofNat_add, BitVec.add_assoc]
      · exact ha.elim
  have whole : AgreesExcept (frame s) s u :=
    (stage.agrees.trans small).mono fun _ hc => (List.mem_append.mp hc).elim id id
  refine ⟨?_, ready, whole, loaded_of_frame pre whole,
    (h.read (r := 4) (n := 64) (by simp)).trans stage.rsp, ?_⟩
  · obtain ⟨n, hn⟩ := stage.execution
    exact ⟨n + fuel, hn.trans run⟩
  · intro saved hsaved
    rw [P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees h]
    · exact stage.saved saved hsaved
    · intro i hi c hc ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, he⟩ := ha
        have hoff : saved.2 ≤ 48 := by
          simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hsaved
          rcases hsaved with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have hs := stack_contains pre (offset := saved.2) (len := 8) (by omega)
          (by omega) ⟨i, hi, rfl⟩
        have hout := memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _)
          (show offset + j < 32 by omega)
        rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← he] at hout
        exact (pre.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)) _ hout hs
      · exact ha.elim

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store
