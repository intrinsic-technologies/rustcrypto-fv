import P256.Proofs.Field.Schoolbook.Entry
import P256.Proofs.Field.Schoolbook.UpperProducts
import P256.Proofs.Field.Schoolbook.UpperSums

set_option autoImplicit false

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec.Program.Routines

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem upper_products_scratch {s t : RamState} (h : (upperProductsEffect s).Holds s t) :
    AgreesExcept (scratchComponents (rspOf s)) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [upperProductsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, or_assoc, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [scratchComponents, Component.isMem]
  · intro a c hc ha
    simp only [upperProductsEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, or_assoc, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact False.elim ha
    all_goals refine ⟨.mem (rspOf s) 88, by simp [scratchComponents], ?_⟩
    all_goals exact scratch_slot_covers (by decide +kernel) ha

theorem upper_low_scratch {s t : RamState} {base : BitVec 64}
    (h : (upperSumsLowEffect s).Holds s t) :
    AgreesExcept (scratchComponents base) s t := by
  apply h.agrees.mono
  simp [upperSumsLowEffect, Effect.components, Write.component, Operand.component, scratchComponents]

theorem upper_middle_scratch {s t : RamState} {base : BitVec 64}
    (h : (upperSumsMiddleEffect s).Holds s t) :
    AgreesExcept (scratchComponents base) s t := by
  apply h.agrees.mono
  simp [upperSumsMiddleEffect, Effect.components, Write.component, Operand.component, scratchComponents]

theorem upper_high_scratch {s t : RamState} {base : BitVec 64}
    (h : (upperSumsHighEffect s).Holds s t) :
    AgreesExcept (scratchComponents base) s t := by
  apply h.agrees.mono
  simp [upperSumsHighEffect, Effect.components, Write.component, Operand.component, scratchComponents]

end P256.Proofs.Field.Schoolbook
