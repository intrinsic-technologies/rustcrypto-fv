import P256.Proofs.Nonce.UpdateValue.Absorb.Buffer.Prepare
import P256.Proofs.Nonce.UpdateValue.Absorb.Buffer.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Absorb.Buffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {state : State}

set_option maxRecDepth 2048 in
theorem block_writes (pre : UpdateValuePre initial boundary state)
    (input : Entered initial s state) : WritesWithin (effect s).components
      #v[region initial] := by
  intro c hc a ha
  have within (offset : Nat) (bound : offset + 8 ≤ 32)
      (covered : (Component.mem (destination s + BitVec.ofNat 64 offset) 8).Covers a) :
      (region initial).Contains a.toNat := by
    obtain ⟨i, hi, rfl⟩ := covered
    rw [destination_sub input, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add (region_bounded pre)
      (Nat.le_refl _) (Nat.le_refl _) (by change offset + i < 64; omega)
  simp only [effect, Effect.components, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component, or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact ⟨_, by simp, within 0 (by decide) (by simpa only [BitVec.add_zero] using ha)⟩
  · exact ⟨_, by simp, within 8 (by decide) ha⟩
  · exact ⟨_, by simp, within 16 (by decide) ha⟩
  · exact ⟨_, by simp, within 24 (by decide) ha⟩

set_option maxRecDepth 2048 in
theorem block_bytes (pre : UpdateValuePre initial boundary state)
    (input : Entered initial s state)
    (holds : (effect s).Holds s t) :
    (MemoryRegion.mk (scratch initial + 168).toNat 32).HasBytes t.external state.value := by
  have srcReadable : MemReadable s (source s) 32 := by
    rw [source_eq input]
    exact state_readable pre input.toFrameState (by decide)
  have dstReadable : MemReadable t (destination s) 32 := by
    apply readable_of_grow ?_ holds.agrees.grow
    rw [destination_eq input]
    exact ScalarFrame.stack_readable pre.callee input.toFrameState (by decide) (by decide)
  have values := holds.writes
  change t.regValue .rax = memLoad s.external (source s) 64 ∧
    t.regValue .rcx = memLoad s.external (source s + 8) 64 ∧
    memLoad t.external (destination s) 64 = memLoad s.external (source s) 64 ∧
    memLoad t.external (destination s + 8) 64 = memLoad s.external (source s + 8) 64 ∧
    memLoad t.external (destination s + 16) 64 = memLoad s.external (source s + 16) 64 ∧
    memLoad t.external (destination s + 24) 64 = memLoad s.external (source s + 24) 64 at values
  have words : ∀ j < 4,
      memLoad t.external (destination s + BitVec.ofNat 64 (8*j)) 64 =
        memLoad s.external (source s + BitVec.ofNat 64 (8*j)) 64 := by
    intro j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using values.2.2.1
    · exact values.2.2.2.1
    · exact values.2.2.2.2.1
    · exact values.2.2.2.2.2
  have copied := HMAC.Key.Output.bytes_of_words srcReadable dstReadable words
  have bytes := hasBytes_copy (target := t.external)
    (b := scratch initial + 168) input.drbg.2 (by
    simpa only [source_eq input, show destination s = scratch initial + 168 from input.bufferPointer,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul] using copied)
  exact bytes

end P256.Proofs.Nonce.UpdateValue.Absorb.Buffer
