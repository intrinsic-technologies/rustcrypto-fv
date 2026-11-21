import P256.Proofs.Verifying.Wrapper.KeyCopy.Tail
import P256.Proofs.Verifying.Wrapper.KeyCopy.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.KeyCopy.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem frame {s t : RamState} (h : (effect s).Holds s t) :
    AgreesExcept [.reg 1,.mem (stackPtr s+63) 2,.mem (stackPtr s+3) 4,.rip] s t := by
  simpa [effect, Effect.components, List.map, List.cons_append, List.nil_append,
    Write.component, Operand.component, stackPtr, Operand.read_reg64, gprIndex] using h.agrees

theorem wide {s t : RamState} (h : (effect s).Holds s t) :
    AgreesExcept (components s) s t := by
  apply (frame h).widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals simp [components, Component.isMem] at *
  · intro a c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    · obtain ⟨i, hi, he⟩ := covered
      refine ⟨.mem (stackPtr s) 65, by simp [components], 63+i, by omega, ?_⟩
      simpa [BitVec.ofNat_add, BitVec.add_assoc] using he
    · obtain ⟨i, hi, he⟩ := covered
      refine ⟨.mem (stackPtr s) 65, by simp [components], 3+i, by omega, ?_⟩
      simpa [BitVec.ofNat_add, BitVec.add_assoc] using he

theorem preserved {s t : RamState} (h : (effect s).Holds s t) {i : Nat}
    (bound : i < 3 ∨ (7 ≤ i ∧ i < 63)) :
    t.external[stackPtr s+BitVec.ofNat 64 i]? = s.external[stackPtr s+BitVec.ofNat 64 i]? := by
  have outside (off len : Nat) (small : off+len ≤ 65) (away : i < off ∨ off+len ≤ i) :
      ¬ (Component.mem (stackPtr s+BitVec.ofNat 64 off) len).Covers
        (stackPtr s+BitVec.ofNat 64 i) := by
    rintro ⟨j,hj,he⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at he
    have eq := (BitVec.add_right_inj _).mp he
    have hn := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
      Nat.mod_eq_of_lt (show off+j < 2^64 by omega)] at hn
    omega
  apply (frame h).byte
  intro c hc covered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  · exact outside 63 2 (by decide) (by omega) covered
  · exact outside 3 4 (by decide) (by omega) covered

end P256.Proofs.Verifying.Wrapper.KeyCopy.Tail
