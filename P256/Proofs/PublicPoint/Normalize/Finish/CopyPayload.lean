import P256.Proofs.PublicPoint.Normalize.Finish.CopyYResult
import P256.Proofs.Field.Representation
import P256.Proofs.Field.Preserve
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem copy_y_agrees {s t : RamState} (effect : (copyYEffect s).Holds s t) :
    AgreesExcept [.reg 0, .reg 1, .mem (stackPtr s + 1064) 33, .rip] s t := by
  apply effect.agrees.widen
  · intro c hc hm
    simp only [copyYEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)|rfl
    all_goals try simp
    all_goals simp [Component.isMem] at hm
  · intro a c hc ha
    simp only [copyYEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)|rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨i, hi, rfl⟩ := ha
    all_goals refine ⟨.mem (stackPtr s + 1064) 33, by simp, ?_⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨8+i, by omega, by
        change (stackPtr s + _) + _ = _
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        congr 1
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        rfl⟩
    · exact ⟨16+i, by omega, by
        change (stackPtr s + _) + _ = _
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        congr 1
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        rfl⟩
    · exact ⟨24+i, by omega, by
        change (stackPtr s + _) + _ = _
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        congr 1
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        rfl⟩
    · exact ⟨32+i, by omega, by
        change (stackPtr s + _) + _ = _
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        congr 1
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        rfl⟩

set_option maxRecDepth 2048 in
theorem copy_y_payload {s t : RamState} {y : Nat}
    (effect : (copyYEffect s).Holds s t)
    (input : MontgomeryAt s (stackPtr s + 32) y)
    (output : MemReadable t (stackPtr s + 1064) 32) :
    MontgomeryAt t (stackPtr s + 1064) y := by
  apply montgomeryAt_of_memLoad_limbs input.1 output.mem
  intro j hj
  apply Eq.trans _ (input.memLoad_limb j hj)
  have values := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at values
  rcases values with ⟨_, _, h0, h8, h16, h24, _⟩
  change memLoad t.external (stackPtr s + 1064) 64 = memLoad s.external (stackPtr s + 32) 64 at h0
  change memLoad t.external (stackPtr s + 1072) 64 = memLoad s.external (stackPtr s + 40) 64 at h8
  change memLoad t.external (stackPtr s + 1080) 64 = memLoad s.external (stackPtr s + 48) 64 at h16
  change memLoad t.external (stackPtr s + 1088) 64 = memLoad s.external (stackPtr s + 56) 64 at h24
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h8
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h16
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h24

theorem copy_y_tag {s t : RamState} (effect : (copyYEffect s).Holds s t)
    (allocated : MemReadable t (stackPtr s + 1096) 1) :
    t.external[stackPtr s + 1096]? = some 0 := by
  have word : memLoad t.external (stackPtr s + 1096) 8 = 0 := effect.writes.2.2.2.2.2.2
  have bytes := Bytes.of_memLoad (n := 8) allocated.mem
  rw [word] at bytes
  simpa [storedByte] using bytes 0 (by decide)

end P256.Proofs.PublicPoint.Normalize.Finish
