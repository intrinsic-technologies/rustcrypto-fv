import P256.Proofs.Field.Schoolbook.LowerSums
import P256.Proofs.Field.Schoolbook.Preservation

set_option autoImplicit false
namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem lowerSums_components (s : RamState) :
    (lowerSumsEffect s).components =
      [.reg 15, .mem (rspOf s) 8, .mem (rspOf s+24#64) 8,
       .reg 8, .reg 9, .reg 14, .mem (rspOf s+40#64) 8,
       .reg 0, .reg 1, .reg 2, .reg 5, .reg 6, .reg 11, .reg 12,
       .mem (rspOf s+56#64) 8, .flags, .rip] := by
  x86_norm [lowerSumsEffect, lowerSumsMiddleEffect, lowerSumsPrefixEffect,
    lowerSumsFirstEffect, lowerSumsSecondEffect, lowerSumsThirdEffect,
    lowerSumsFourthEffect, savedSource, BitVec.add_zero, Bool.or_eq_false_iff, Bool.or_eq_true_iff]

theorem lowerSums_scratch {s t : RamState} (h : (lowerSumsEffect s).Holds s t) :
    AgreesExcept (scratchComponents (rspOf s)) s t := by
  apply h.agrees.widen
  · intro c hc hm
    rw [lowerSums_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [scratchComponents, Component.isMem]
  · intro a c hc ha
    rw [lowerSums_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact False.elim ha
    all_goals refine ⟨.mem (rspOf s) 88, by simp [scratchComponents], ?_⟩
    · apply scratch_slot_covers (c := 0#64) (by decide +kernel)
      simpa only [BitVec.add_zero] using ha
    all_goals exact scratch_slot_covers (by decide +kernel) ha

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem lowerSums_source {s t : RamState} (h : (lowerSumsEffect s).Holds s t) :
    t.regValue .rsi = savedSource s := by
  have hw := Write.allHold_iff.mp h.writes
    (⟨(Operand.reg 6 : Operand 64), savedSource ((lowerSumsMiddleEffect s).after s true)⟩ : Write)
    (List.mem_append_right _ (by simp [lowerSumsFourthEffect, savedSource]))
  change (Operand.reg 6 : Operand 64).read t = _
  rw [hw]
  x86_norm [lowerSumsMiddleEffect, lowerSumsPrefixEffect,
    lowerSumsFirstEffect, lowerSumsSecondEffect, lowerSumsThirdEffect,
    savedSource, BitVec.add_zero, Bool.or_eq_false_iff, Bool.or_eq_true_iff]

theorem lowerSums_memory_after (e : Effect) (s : RamState) (a : BitVec 64)
    (apart : ∀ i < 8, ∀ c ∈ e.components, ¬ c.Covers (a+BitVec.ofNat 64 i)) :
    (Operand.mem a : Operand 64).read (e.after s true) = (Operand.mem a : Operand 64).read s := by
  rw [Effect.read_after]
  change memLoad (applyWrites s e.writes).external a 64 = memLoad s.external a 64
  apply memLoad_congr
  intro i hi
  let o : RamState → UInt8 := fun t => memByte t.external (a+BitVec.ofNat 64 i)
  change o (applyWrites s e.writes) = o s
  apply applyWrites_obs o (o s) _ _ _ (.inl rfl)
  intro w hw t
  rcases w with @⟨n, dst, val⟩
  cases dst with
  | mem b =>
    refine .inl ?_
    simp only [o, Write.apply_mk, Operand.write, memByte, PhysicalMemory.read]
    rw [memStore_getElem?_of_ne]
    intro j hj he
    exact apart i hi (.mem b (n/8)) (Effect.mem_components.mpr (.inl ⟨_, hw, rfl⟩))
      ⟨j, hj, he.symm⟩
  | _ => exact .inl rfl

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem lowerSums_source_limb {s t : RamState} (pre : LowerSumsPre 0x11c9f6 122 s)
    (h : (lowerSumsEffect s).Holds s t) :
    t.regValue .rcx = memLoad s.external (savedSource s+24#64) 64 := by
  have hw := Write.allHold_iff.mp h.writes
    (⟨(Operand.reg 1 : Operand 64),
      (Operand.mem (savedSource ((lowerSumsMiddleEffect s).after s true)+24#64) : Operand 64).read
        ((lowerSumsMiddleEffect s).after s true)⟩ : Write)
    (List.mem_append_right _ (by simp [lowerSumsFourthEffect]))
  have src : savedSource ((lowerSumsMiddleEffect s).after s true) = savedSource s := by
    x86_norm [lowerSumsMiddleEffect, lowerSumsPrefixEffect,
      lowerSumsFirstEffect, lowerSumsSecondEffect, lowerSumsThirdEffect,
      savedSource, BitVec.add_zero, Bool.or_eq_false_iff, Bool.or_eq_true_iff]
  change (Operand.reg 1 : Operand 64).read t = _
  rw [hw, src]
  generalize he : savedSource s+24#64 = address
  have hap : RangeApart (rspOf s) 88 address 8 := he ▸ pre.apart
  apply lowerSums_memory_after
  intro i hi c hc hcov
  have hc' : c ∈
      [.reg 1, .reg 5, .reg 15, .reg 6, .reg 11,
       .mem (rspOf s) 8, .mem (rspOf s+24#64) 8,
       .reg 0, .reg 2, .reg 8, .reg 9, .reg 14, .mem (rspOf s+40#64) 8, .flags, .rip] := by
    have ec : (lowerSumsMiddleEffect s).components =
        [.reg 1, .reg 5, .reg 15, .reg 6, .reg 11,
         .mem (rspOf s) 8, .mem (rspOf s+24#64) 8,
         .reg 0, .reg 2, .reg 8, .reg 9, .reg 14, .mem (rspOf s+40#64) 8, .flags, .rip] := by
      x86_norm [lowerSumsMiddleEffect, lowerSumsPrefixEffect,
        lowerSumsFirstEffect, lowerSumsSecondEffect, lowerSumsThirdEffect,
        BitVec.add_zero, Bool.or_eq_false_iff, Bool.or_eq_true_iff]
    exact ec ▸ hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim hcov
  all_goals obtain ⟨j, hj, he⟩ := hcov
  · exact hap j (by omega) i hi he.symm
  · have e := hap (24+j) (by omega) i hi
    apply e
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he.symm
  · have e := hap (40+j) (by omega) i hi
    apply e
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he.symm

theorem lowerSums_rip {s t : RamState} (h : (lowerSumsEffect s).Holds s t) : t.RIP = 0x11ca70 :=
  h.rip

end P256.Proofs.Field.Schoolbook
