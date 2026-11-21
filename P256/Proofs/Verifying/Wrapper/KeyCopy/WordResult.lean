import P256.Proofs.Verifying.Wrapper.KeyCopy.Word
import P256.Proofs.Verifying.Wrapper.KeyCopy.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.KeyCopy.Word

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem frame {s t : RamState} {pc : BitVec 64} {off : BitVec 8}
    (h : (effect pc off s).Holds s t) :
    AgreesExcept [.reg 1, .mem (stackPtr s + off.signExtend 64) 8, .rip] s t := by
  simpa [effect, Effect.components, List.map, List.cons_append, List.nil_append,
    Write.component, Operand.component, stackPtr, Operand.read_reg64, gprIndex] using h.agrees

theorem wide {s t : RamState} {pc : BitVec 64} {off : BitVec 8} {offset : Nat}
    (h : (effect pc off s).Holds s t) (offsetEq : off.signExtend 64 = BitVec.ofNat 64 offset)
    (bound : offset+8 ≤ 65) : AgreesExcept (components s) s t := by
  apply (frame h).widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals simp [components, Component.isMem] at *
  · intro a c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨i, hi, he⟩ := covered
    refine ⟨.mem (stackPtr s) 65, by simp [components], offset+i, by omega, ?_⟩
    simpa only [offsetEq, BitVec.ofNat_add, BitVec.add_assoc] using he

theorem preceding {s t : RamState} {pc : BitVec 64} {off : BitVec 8} {offset i : Nat}
    (h : (effect pc off s).Holds s t) (offsetEq : off.signExtend 64 = BitVec.ofNat 64 offset)
    (bound : offset+8 ≤ 65) (before : i < offset) :
    t.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 i]? := by
  apply (frame h).byte
  intro c hc covered
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j, hj, he⟩ := covered
  rw [offsetEq, BitVec.add_assoc, ← BitVec.ofNat_add] at he
  have eq : BitVec.ofNat 64 i = BitVec.ofNat 64 (offset+j) := by
    exact (BitVec.add_right_inj _).mp he
  have hn := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
    Nat.mod_eq_of_lt (show offset+j < 2^64 by omega)] at hn
  omega

theorem copied {s t : RamState} {pc pc' : BitVec 64} {off : BitVec 8} {offset : Nat}
    (pre : KeyCopy.Pre pc' s) (h : (effect pc off s).Holds s t)
    (offsetEq : off.signExtend 64 = BitVec.ofNat 64 offset) (bound : offset+8 ≤ 65) :
    ∀ i < 8, t.external[stackPtr s + BitVec.ofNat 64 (offset+i)]? =
      s.external[s.regValue .rdx + BitVec.ofNat 64 (offset+i)]? := by
  apply chunk_bytes pre h.agrees.grow offset 64 bound
  have hw := h.writes.2
  change memLoad t.external (stackPtr s + off.signExtend 64) 64 =
    memLoad s.external (s.regValue .rdx + off.signExtend 64) 64 at hw
  simpa only [offsetEq] using hw

end P256.Proofs.Verifying.Wrapper.KeyCopy.Word
