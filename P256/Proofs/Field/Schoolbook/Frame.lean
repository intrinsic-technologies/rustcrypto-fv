import P256.Proofs.Field.Interface
import P256.Proofs.Program.Stack
import X86Proofs.Program.Compose

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Field.Schoolbook

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ScratchPre (p : BitVec 64) (codeLen : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : ∀ c : BitVec 64, SlotIn c 8 0 88 → MemWritable s (rspOf s+c) 8
  codeApart : ∀ c : BitVec 64, SlotIn c 8 0 88 → RangeApart (rspOf s+c) 8 p codeLen

namespace ScratchPre

variable {p : BitVec 64} {codeLen : Nat} {s : RamState}

theorem readable (h : ScratchPre p codeLen s) (c : BitVec 64) (hc : SlotIn c 8 0 88) :
    MemReadable s (rspOf s+c) 8 := (h.writable c hc).readable

theorem apart (h : ScratchPre p codeLen s) (c : BitVec 64) (hc : SlotIn c 8 0 88)
    (off len : Nat) (hbound : off+len ≤ codeLen) :
    RangeApart (rspOf s+c) 8 (p+BitVec.ofNat 64 off) len := by
  intro i hi j hj
  have hap := h.codeApart c hc i hi (off+j) (by omega)
  simpa only [BitVec.add_assoc, BitVec.ofNat_add] using hap

theorem apart0 (h : ScratchPre p codeLen s) (c : BitVec 64) (hc : SlotIn c 8 0 88)
    (len : Nat) (hbound : len ≤ codeLen) : RangeApart (rspOf s+c) 8 p len := by
  simpa using
    h.apart c hc 0 len (by omega)

end ScratchPre

theorem scratch_slot_address {s t : RamState} (hsp : rspOf t = stackPtr s-136)
    (c : BitVec 64) (hc : SlotIn c 8 0 88) :
    rspOf t+c = stackPtr s-BitVec.ofNat 64 (136-c.toNat) := by
  have hcn : c.toNat ≤ 80 := by
    have h := hc
    simp only [SlotIn, BitVec.add_zero] at h
    omega
  rw [hsp, ← BitVec.ofNat_sub_ofNat_of_le 136 c.toNat c.isLt (by omega)]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem scratch_slot_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SchoolbookPre s boundary)
    (hsp : rspOf t = stackPtr s-136)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (c : BitVec 64) (hc : SlotIn c 8 0 88) : MemWritable t (rspOf t+c) 8 := by
  have hcn : c.toNat + 8 ≤ 88 := by simpa only [SlotIn, BitVec.add_zero] using hc
  rw [scratch_slot_address hsp c hc]
  apply writable_of_grow (hw := ?_) grow
  have hr := stack_sub_readable pre.stack (offset := 136-c.toNat) (len := 8)
    (by omega) (by omega)
  apply MemWritable.of_not_reserved (by decide) hr.low hr.mem
  intro i hi hres
  apply pre.avoids (Stack.region s 136) (by simp) _ ?_ (.inr hres)
  apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
  · rw [stack_sub_toNat pre.stack (by omega)]
    change (stackPtr s).toNat-136 ≤ (stackPtr s).toNat-(136-c.toNat)
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack (by omega)]
    have hs := (stack_bounds pre.stack).1
    omega

theorem scratch_slot_contains [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SchoolbookPre s boundary)
    (hsp : rspOf t = stackPtr s-136)
    (c : BitVec 64) (hc : SlotIn c 8 0 88) {i : Nat} (hi : i < 8) :
    (Stack.region s 136).Contains (rspOf t+c+BitVec.ofNat 64 i).toNat := by
  have hcn : c.toNat + 8 ≤ 88 := by simpa only [SlotIn, BitVec.add_zero] using hc
  rw [scratch_slot_address hsp c hc]
  apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
  · rw [stack_sub_toNat pre.stack (by omega)]
    change (stackPtr s).toNat-136 ≤ (stackPtr s).toNat-(136-c.toNat)
    omega
  · rw [stack_region_end, stack_sub_toNat pre.stack (by omega)]
    have hs := (stack_bounds pre.stack).1
    omega

theorem scratchPre_of_callee [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {p : BitVec 64} {codeLen : Nat}
    (pre : SchoolbookPre s boundary)
    (hip : t.RIP = p) (hsp : rspOf t = stackPtr s-136)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (code : ∀ j < codeLen, InProgram (p+BitVec.ofNat 64 j)) :
    ScratchPre p codeLen t := by
  refine ⟨hip, scratch_slot_writable pre hsp grow, ?_⟩
  intro c hc i hi j hj he
  have hs := scratch_slot_contains pre hsp c hc hi
  apply pre.avoids (Stack.region s 136) (by simp) _ hs
  rw [he]
  exact Or.inl (code j hj)

macro "schoolbook_frame" : tactic => `(tactic| first
  | exact P256.Proofs.Field.Schoolbook.ScratchPre.readable
      (by assumption) _ (by decide +kernel)
  | exact P256.Proofs.Field.Schoolbook.ScratchPre.writable
      (by assumption) _ (by decide +kernel)
  | exact P256.Proofs.Field.Schoolbook.ScratchPre.apart
      (by assumption) _ (by decide +kernel) _ _ (by decide +kernel)
  | exact P256.Proofs.Field.Schoolbook.ScratchPre.apart0
      (by assumption) _ (by decide +kernel) _ (by decide +kernel))

macro "schoolbook_avoid" : tactic => `(tactic| (
  apply X86Proofs.Effect.avoids_codeRange
  x86_norm
  all_goals (first | trivial | schoolbook_frame)))

end P256.Proofs.Field.Schoolbook
