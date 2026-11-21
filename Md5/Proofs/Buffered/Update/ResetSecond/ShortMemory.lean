import Md5.Proofs.Buffered.Update.Short.Memory

namespace Md5.Proofs.Buffered.ResetSecond

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem short_finish_update_agrees {kind : UpdateKind} {initial s t : RamState}
    (hsp : stackPtr s = stackPtr initial)
    (ha : AgreesExcept [.reg kind.sizeRegister, .flags, .rip, .mem (kind.context s + 63) 1] s t) :
    AgreesExcept (kind.changes initial) s t := by
  apply ha.widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals cases kind <;> simp_all [UpdateKind.changes, UpdateKind.workRegisters,
      UpdateKind.sizeRegister, Component.isMem]
  · intro address c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    have hi0 : i = 0 := by omega
    subst i
    refine ⟨.mem (kind.context initial) 88,
      by simp [UpdateKind.changes], 63, by decide, ?_⟩
    simp only [UpdateKind.context, UpdateKind.contextOffset, BitVec.add_zero, hsp]
    rfl

end Md5.Proofs.Buffered.ResetSecond
