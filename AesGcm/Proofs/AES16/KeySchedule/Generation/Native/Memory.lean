import AesGcm.Proofs.AES16.KeySchedule.Generation.Memory
import AesGcm.Proofs.Machine.Runtime.Frame

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem push_writable {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) : Writable code mem (sp - 8) 8 := by
  apply h.hstack.sub
  · have := h.hroom
    rw [stack_sub_toNat h]
    bv_omega
  · have := h.hroom
    rw [stack_sub_toNat h]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega

theorem schedule_writable {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) :
    Writable code mem (base use256 sp) (if use256 then 240 else 176) := by
  apply h.hstack.sub
  all_goals rw [base_toNat h, stack_sub_toNat h]
  all_goals have := h.hroom
  all_goals cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem round_bound (use256 : Bool) (round : Nat) (hr : round ≤ (variant use256).Nr) :
    16 * round + 16 ≤ (if use256 then 240 else 176) := by
  cases use256 <;> simp only [variant, Variant.Nr, Bool.false_eq_true, ↓reduceIte] at * <;> omega

theorem round_writable {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) (round : Nat) (hr : round ≤ (variant use256).Nr) :
    Writable code mem (base use256 sp + BitVec.ofNat 64 (16 * round)) 16 := by
  apply (schedule_writable h).sub
  all_goals rw [address_toNat h (16 * round) (by have := round_bound use256 round hr; omega),
    base_toNat h]
  · omega
  · have := round_bound use256 round hr
    omega

theorem push_frame {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) (round : Nat) (ret : BitVec 64) :
    RamWriteFrame mem (memStore mem (sp - 8) ret) (roundRegions use256 sp round) := by
  apply (RamWriteFrame.refl _ _).memStore ret
  refine ⟨span (sp - 248) 248, List.Mem.head _, ?_⟩
  have hs : (sp - 8).toNat = sp.toNat - 8 := by have := h.hroom; bv_omega
  simp only [InRegion, span, stack_sub_toNat h, hs]
  have := h.hroom
  have := stack_limit h
  cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega

theorem round_stack_within {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) (round : Nat) (hr : round ≤ (variant use256).Nr) :
    RegionsWithin (roundRegions use256 sp round)
      [span (sp - 248) (if use256 then 608 else 512)] := by
  intro r hin
  obtain ⟨r', hr', hlow, hhigh⟩ := roundRegions_within h round hr r hin
  obtain ⟨r'', hr'', hlow', hhigh'⟩ := regions_within_stack h r' hr'
  exact ⟨r'', hr'', Nat.le_trans hlow' hlow, Nat.le_trans hhigh hhigh'⟩

theorem previous_outside {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) (round oldRound : Nat)
    (hr : round ≤ (variant use256).Nr) (hold : oldRound < round) :
    Outside (roundRegions use256 sp round)
      (base use256 sp + BitVec.ofNat 64 (16 * oldRound)) 16 := by
  have hbound := round_bound use256 round hr
  have ha := address_toNat h (16 * oldRound) (by omega)
  have hn := address_toNat h (16 * round) (by omega)
  refine ⟨?_, ?_⟩
  · rw [ha]
    have := stack_limit h
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
  · intro region hregion
    simp only [roundRegions, List.mem_cons, List.not_mem_nil, or_false] at hregion
    rcases hregion with rfl | rfl
    · simp only [span, ha, stack_sub_toNat h]
      have := h.hroom
      omega
    · simp only [span, ha, hn]
      omega

theorem prefix_of_frame {use256 : Bool} {code : CodeMap} {before after : Ram}
    {sp : BitVec 64} (h : MemoryReady use256 code before sp)
    (key : Vector UInt8 (variant use256).keyBytes) (round : Nat)
    (hr : round ≤ (variant use256).Nr)
    (hp : RawSchedulePrefix (variant use256) key round (base use256 sp) before)
    (hf : RamWriteFrame before after (roundRegions use256 sp round)) :
    RawSchedulePrefix (variant use256) key round (base use256 sp) after := by
  intro r hr' p
  have hout := previous_outside h round r.val hr hr'
  have hout' : Outside (roundRegions use256 sp round)
      ((base use256 sp + BitVec.ofNat 64 (16 * r.val)) + BitVec.ofNat 64 (2 * p.val)) 2 := by
    have hbound := round_bound use256 round hr
    have ha := address_toNat h (16 * r.val) (by omega)
    have hap := address_toNat h (16 * r.val + 2 * p.val) (by have := p.isLt; omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at hap
    refine ⟨?_, ?_⟩
    · rw [hap]
      have := stack_limit h
      have := p.isLt
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
    · intro region hin
      have houtRegion := hout.2 region hin
      rw [hap]
      rw [ha] at houtRegion
      have := p.isLt
      omega
  rw [show base use256 sp + BitVec.ofNat 64 (16 * r.val + 2 * p.val) =
    (base use256 sp + BitVec.ofNat 64 (16 * r.val)) + BitVec.ofNat 64 (2 * p.val) by
      rw [BitVec.ofNat_add, BitVec.add_assoc], hf.memLoad_eq hout']
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hp r hr' p

theorem push_load {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) (ret : BitVec 64) (off : Nat)
    (hoff : off + 2 ≤ (if use256 then 240 else 176)) :
    memLoad (memStore mem (sp - 8) ret) (base use256 sp + BitVec.ofNat 64 off) 16 =
      memLoad mem (base use256 sp + BitVec.ofNat 64 off) 16 := by
  apply memLoad_memStore_of_rangeApart
  apply RangeApart.of_toNat
  · have := h.hroom
    have := stack_limit h
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  · rw [address_toNat h off (by omega)]
    have := stack_limit h
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
  · left
    rw [address_toNat h off (by omega)]
    have := h.hroom
    bv_omega

theorem callStack_disjoint {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) (args : Values Value Reg.count)
    (ret : BitVec 64) (hsp : args[4].get 64 = sp - 8) (off len : Nat)
    (hoff : off ≤ (if use256 then 240 else 176)) :
    (callStack (activationOfValues mem args ret (sp - 248))).Disjoint
      (span (base use256 sp + BitVec.ofNat 64 off) len) := by
  have hs : (sp - 8).toNat = sp.toNat - 8 := by have := h.hroom; bv_omega
  intro x hx hy
  simp only [callStack, activationOfValues, hsp, MemoryRegion.Contains,
    stack_sub_toNat h, hs] at hx
  simp only [span, MemoryRegion.Contains, address_toNat h off hoff] at hy
  have := h.hroom
  omega

theorem callee_within {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (h : MemoryReady use256 code mem sp) (args : Values Value Reg.count)
    (ret : BitVec 64) (hsp : args[4].get 64 = sp - 8) (round : Nat) :
    RegionsWithin
      [(activationOfValues mem args ret (sp - 248)).region,
        span (base use256 sp + BitVec.ofNat 64 (16 * round)) 16]
      (roundRegions use256 sp round) := by
  intro region hregion
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hregion
  rcases hregion with rfl | rfl
  · refine ⟨span (sp - 248) 248, List.Mem.head _, ?_, ?_⟩
    · exact Nat.le_refl _
    · simp only [Activation.region, activationOfValues, hsp, span, stack_sub_toNat h]
      have := h.hroom
      bv_omega
  · exact ⟨_, List.Mem.tail _ (List.Mem.head _), Nat.le_refl _, Nat.le_refl _⟩

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native
