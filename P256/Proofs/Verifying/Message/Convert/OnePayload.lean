import P256.Proofs.Verifying.Message.Convert.One
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Convert.One

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def components (destination : BitVec 64) : List Component :=
  [.reg 0, .reg 14, .rip, .mem destination 32]

theorem frame {s t : RamState} (h : (effect s).Holds s t) :
    AgreesExcept (components (destination s)) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [components]
    all_goals simp [Component.isMem] at hm
  · intro a c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (destination s) 32, by simp [components], ?_⟩
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩

theorem output {s t : RamState} {value : Nat}
    (result : (effect s).Holds s t) (input : MontgomeryAt s (source s) value)
    (allocated : MemReadable t (destination s) 32) : MontgomeryAt t (destination s) value := by
  apply montgomeryAt_of_memLoad_limbs input.1 allocated.mem
  intro j hj
  apply Eq.trans _ (input.memLoad_limb j hj)
  have values := result.writes
  simp only [effect, Write.AllHold, Operand.read] at values
  obtain ⟨_, _, h0, h8, h16, h24⟩ := values
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] using h8
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] using h16
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat] using h24

end P256.Proofs.Verifying.Message.Convert.One
