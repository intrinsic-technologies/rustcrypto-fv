import AesGcm.Proofs.AES16.KeySchedule.Input
import AesGcm.Proofs.AES16.KeySchedule.Generation.Memory
import AesGcm.Proofs.Machine.Runtime.Frame

namespace AesGcm.Proofs.Machine.AES16.KeySchedule
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Generation

theorem input_call_pre {use256 later : Bool} {code : CodeMap} {mem : Ram}
    {sp : BitVec 64} (h : MemoryReady use256 code mem sp)
    (args : Values Value Reg.count) (ret : BitVec 64)
    (hs : args[4].get 64 = sp - 8)
    (hd : args[7].get 64 = sp + (if use256 then 12 else 8) + (if later then 16 else 0))
    (hn : args[6].get 64 = 8)
    (hr : args[2].get 64 = sp + (if use256 then 288 else 200)) :
    let fr := activationOfValues mem args ret (sp - 248)
    fr.rsi = 8 ∧ Readable mem fr.rdx 16 ∧ Writable code mem fr.rdi 16 ∧
      (callStack fr).Disjoint (span fr.rdi 16) ∧
      (callStack fr).Disjoint (span fr.rdx 16) ∧
      (span fr.rdi 16).Disjoint (span fr.rdx 16) := by
  have hlim := stack_limit h
  have hroom := h.hroom
  have hlow := stack_sub_toNat h
  have hsp : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
  have hraw : (sp + (if use256 then 288 else 200)).toNat =
      sp.toNat + (if use256 then 288 else 200) := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have hdst : (sp + (if use256 then 12 else 8) + (if later then 16 else 0)).toNat =
      sp.toNat + (if use256 then 12 else 8) + (if later then 16 else 0) := by
    cases use256 <;> cases later <;>
      simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  dsimp only [activationOfValues]
  rw [hn, hr, hd]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · apply h.hstack.readable.sub
    · rw [hlow, hraw]; omega
    · rw [hlow, hraw]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · apply h.hstack.sub
    · rw [hlow, hdst]; omega
    · rw [hlow, hdst]
      cases use256 <;> cases later <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · intro a ha hb
    simp only [callStack, MemoryRegion.Contains, span, hs, hsp, hlow, hdst] at ha hb
    cases use256 <;> cases later <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
  · intro a ha hb
    simp only [callStack, MemoryRegion.Contains, span, hs, hsp, hlow, hraw] at ha hb
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
  · intro a ha hb
    simp only [MemoryRegion.Contains, span, hraw, hdst] at ha hb
    cases use256 <;> cases later <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega

end AesGcm.Proofs.Machine.AES16.KeySchedule
