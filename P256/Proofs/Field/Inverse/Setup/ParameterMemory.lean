import P256.Proofs.Field.Inverse.Setup.Run
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

set_option exponentiation.threshold 512 in
def parameterValue (i : Fin 8) : BitVec 64 :=
  if i.val < 4 then BitVec.ofNat 64 (P256.Spec.Operations.domain.p / 2^(64*(3-i.val)))
  else BitVec.ofNat 64 ((2^512 % P256.Spec.Operations.domain.p) / 2^(64*(i.val-4)))

def CopiedParameters (s t : RamState) (count : Nat) : Prop :=
  ∀ i : Fin 8, i.val < count →
    memLoad t.external (stackPtr s-168 + BitVec.ofNat 64 (parameterOffset i)) 64 = parameterValue i

theorem parameter_source_value {t : RamState} (loaded : ProgramLoaded t) (i : Fin 8) :
    memLoad t.external (parameterSource i) 64 = parameterValue i := by
  have code : ∀ i : Fin 8, ∀ j : Fin 8,
      Extracted.programSections.fetchByte (parameterSource i + BitVec.ofNat 64 j.val) =
        some (storedByte (parameterValue i) j.val) := by decide +kernel
  have bytes : Bytes t.external (parameterSource i) 8 (storedByte (parameterValue i)) := by
    intro j hj
    exact loaded _ _ (code i ⟨j, hj⟩)
  exact bytes.memLoad (by decide) (by decide)

theorem copied_parameters_word {s t u : RamState} (sp : stackPtr t = stackPtr s-168)
    (loaded : ProgramLoaded t) (i : Fin 8) (before : CopiedParameters s t i.val)
    (effect : (wordEffect i t).Holds t u) : CopiedParameters s u (i.val+1) := by
  have offsets : ∀ i : Fin 8,
      parameterWords[i].2.2.signExtend 64 = BitVec.ofNat 64 (parameterOffset i) := by decide +kernel
  intro j hj
  by_cases same : j = i
  · subst j
    have h := effect.writes.2
    change memLoad u.external (stackPtr t + parameterWords[i].2.2.signExtend 64) 64 =
      memLoad t.external (parameterSource i) 64 at h
    rw [offsets i, sp] at h
    exact h.trans (parameter_source_value loaded i)
  · have ag : AgreesExcept [.reg 0,
        .mem (stackPtr s-168 + BitVec.ofNat 64 (parameterOffset i)) 8, .rip] t u := by
      have ag : AgreesExcept [.reg 0, .mem (stackPtr t + parameterWords[i].2.2.signExtend 64) 8, .rip] t u := by
        simpa [wordEffect, RipCopy.effect, Effect.components, stackPtr, gprIndex] using effect.agrees
      rw [offsets i, sp] at ag
      exact ag
    rw [memLoad_agrees_apart ag ?_]
    · exact before j (by have hn : j.val ≠ i.val := fun h => same (Fin.ext h); omega)
    · intro a len ha
      have eq : a = stackPtr s-168 + BitVec.ofNat 64 (parameterOffset i) ∧ len = 8 := by
        simpa using ha
      rcases eq with ⟨rfl, rfl⟩
      have facts : ∀ i j : Fin 8, i ≠ j →
          parameterOffset i+8 ≤ parameterOffset j ∨ parameterOffset j+8 ≤ parameterOffset i := by
        decide +kernel
      have bound : ∀ i : Fin 8, parameterOffset i+8 ≤ 2^64 := by decide +kernel
      exact RangeApart.offsets _ (bound i) (bound j) (facts i j (Ne.symm same))

theorem copied_parameters_middle {s t u : RamState} {count : Nat}
    (sp : stackPtr t = stackPtr s-168) (before : CopiedParameters s t count)
    (effect : (parameterMiddleEffect t).Holds t u) : CopiedParameters s u count := by
  have ag : AgreesExcept [.mem (stackPtr s-168+104) 8, .reg 8, .rip] t u := by
    have ag : AgreesExcept [.mem (stackPtr t+104) 8, .reg 8, .rip] t u := by
      simpa [parameterMiddleEffect, Effect.components, stackPtr, gprIndex] using effect.agrees
    rw [sp] at ag
    exact ag
  intro i hi
  rw [memLoad_agrees_apart ag ?_]
  · exact before i hi
  · intro a len ha
    have eq : a = stackPtr s-168+104 ∧ len = 8 := by simpa using ha
    rcases eq with ⟨rfl,rfl⟩
    have bound : ∀ i : Fin 8, parameterOffset i+8 ≤ 104 := by decide +kernel
    exact RangeApart.offsets _ (by decide) (by have := bound i; omega) (Or.inr (bound i))

theorem copied_parameters_arguments {s t u : RamState} {count : Nat}
    (before : CopiedParameters s t count) (effect : (parameterArgumentEffect t).Holds t u) :
    CopiedParameters s u count := by
  have memory := effect.agrees.external (by simp [parameterArgumentEffect, Effect.components, Component.Covers])
  intro i hi
  rw [memory]
  exact before i hi

end P256.Proofs.Field.Inverse
