import Md5.Proofs.Buffered.Finalize.Digest.Long.Contracts
import Md5.Proofs.Buffered.Finalize.Digest.Long.Compression
import Md5.Proofs.Buffered.Finalize.Digest.Long.Clear

namespace Md5.Proofs.Buffered.Finalize.Digest.Long

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem compression_agrees {s t : RamState}
    (hdi : s.regValue .rdi = stackPtr s + 8)
    (h : AgreesExcept (FinalizeReset.CompressCall.changes s) s t) :
    AgreesExcept (changes s) s t := by
  apply h.widen
  · intro c hc hm
    simp only [FinalizeReset.CompressCall.changes, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [changes, Component.isMem]
  · intro a c hc ha
    simp only [FinalizeReset.CompressCall.changes, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · refine ⟨.mem (stackPtr s + 8) 168, by simp [changes], ?_⟩
      rw [hdi] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact ⟨i, by omega, rfl⟩
    · exact ⟨.mem (stackPtr s - 320) 320, by simp [changes], ha⟩

theorem clear_agrees {s t : RamState} (h : (Clear.effect s).Holds s t) :
    AgreesExcept (changes s) s t := by
  apply (Clear.effect_agrees h).widen
  · intro c hc hm
    simp only [Clear.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals simp_all [changes, Component.isMem]
  · intro a c hc ha
    simp only [Clear.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ha.elim
    · refine ⟨.mem (stackPtr s + 8) 168, by simp [changes], ?_⟩
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨16 + i, by omega, ?_⟩
      simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
      congr 1
      rw [BitVec.add_assoc]
      rfl

end Md5.Proofs.Buffered.Finalize.Digest.Long
