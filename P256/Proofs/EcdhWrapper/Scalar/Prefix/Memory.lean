import P256.Proofs.EcdhWrapper.Scalar.Prefix.Interface

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prefix_work_frame {initial s t : RamState} {saved : Nat}
    (stack : Stack.Valid initial 4104)
    (frame : MemoryWriteFrame s t #v[ScalarFrame.Work.region initial 4104 saved]) :
    MemoryWriteFrame s t (wrapperRegions ecdhDiffieHellman initial) := by
  intro a ha
  apply frame a
  intro r hr hit
  have eq : r = ScalarFrame.Work.region initial 4104 saved := by simpa using hr
  subst r
  apply ha (callStack ecdhDiffieHellman initial) (by simp [wrapperRegions])
  apply stack_contains_callStack
  have hb := stack_bounds stack
  change (stackPtr initial).toNat-4104 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat-4104+(4104-saved) at hit
  change (stackPtr initial).toNat-4104 ≤ a.toNat ∧
    a.toNat < (Stack.region initial 4104).start+(Stack.region initial 4104).size
  rw [stack_region_end]
  constructor <;> omega

theorem clear_agrees {initial s t : RamState} (rsp : stackPtr s = stackPtr initial-504)
    (effect : (clearEffect s).Holds s t) :
    AgreesExcept [.mem (stackPtr initial-432) 8,.mem (stackPtr initial-440) 8,
      .mem (stackPtr initial-448) 8,.mem (stackPtr initial-456) 8,.rip] s t := by
  simpa only [clearEffect,Effect.components,List.map_cons,List.map_nil,Write.component_mem,
    Nat.reduceDiv,List.cons_append,List.nil_append,rsp,BitVec.sub_eq_add_neg,BitVec.add_assoc,
    BitVec.reduceNeg,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using effect.agrees

theorem prefix_middle_word {initial s t : RamState} {offset : Nat}
    (stack : Stack.Valid initial 4104)
    (g : AgreesExcept ([.mem (stackPtr initial-432) 8,.mem (stackPtr initial-440) 8,
      .mem (stackPtr initial-448) 8,.mem (stackPtr initial-456) 8,.rip] ++ selectComponents initial) s t)
    (range : offset ≤ 48 ∨ offset = 464 ∨ offset = 472) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
  apply memLoad_agrees_apart g
  intro a n member
  have cases : (a = stackPtr initial-432 ∧ n = 8) ∨ (a = stackPtr initial-440 ∧ n = 8) ∨
      (a = stackPtr initial-448 ∧ n = 8) ∨ (a = stackPtr initial-456 ∧ n = 8) ∨
      (a = stackPtr initial-512 ∧ n = 8) := by simpa [selectComponents] using member
  rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · apply stack_sub_apart stack (a := 432) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 440) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 448) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 456) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 512) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega

theorem prefix_nonzero_word {initial s t : RamState} {offset : Nat}
    (stack : Stack.Valid initial 4104) (g : AgreesExcept (Nonzero.clobbers initial) s t)
    (range : offset ≤ 48 ∨ offset = 464 ∨ offset = 472) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
  apply memLoad_agrees_apart g
  intro a n member
  have cases : (a = stackPtr initial-312 ∧ n = 8) ∨ (a = stackPtr initial-320 ∧ n = 8) ∨
      (a = stackPtr initial-328 ∧ n = 8) ∨ (a = stackPtr initial-336 ∧ n = 8) ∨
      (a = stackPtr initial-512 ∧ n = 8) ∨ (a = stackPtr initial-520 ∧ n = 8) ∨
      (a = stackPtr initial-528 ∧ n = 8) ∨ (a = stackPtr initial-513 ∧ n = 1) := by
    simpa [Nonzero.clobbers] using member
  rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · apply stack_sub_apart stack (a := 312) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 320) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 328) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 336) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 512) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 520) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 528) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega
  · apply stack_sub_apart stack (a := 513) (b := offset) (by decide) (by omega) (by decide) (by omega)
    rcases range with h | rfl | rfl <;> omega

end P256.Proofs.EcdhWrapper.Scalar
