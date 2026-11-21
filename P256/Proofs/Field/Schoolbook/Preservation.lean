import P256.Proofs.Field.Schoolbook.Frame
import P256.Proofs.Program.State

set_option autoImplicit false

open P256.Proofs.Program (CalleePre memoryRegion_contains_add stack_region_end)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec.Program.Routines

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def scratchComponents (base : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 8, .reg 9,
   .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15,
   .flags, .rip, .mem base 88]

theorem scratch_slot_covers {base c address : BitVec 64}
    (hc : SlotIn c 8 0 88)
    (h : (Component.mem (base+c) 8).Covers address) :
    (Component.mem base 88).Covers address := by
  obtain ⟨i, hi, rfl⟩ := h
  have hc' : c.toNat+8 ≤ 88 := by simpa only [SlotIn, BitVec.add_zero] using hc
  refine ⟨c.toNat+i, by omega, ?_⟩
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]

theorem scratchComponents_within [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : SchoolbookPre s boundary) :
    WritesWithin (scratchComponents (stackPtr s-136))
      #v[registerRegion s .rdi 64, Stack.region s 136] := by
  have hsp := stack_sub_toNat pre.stack (offset := 136) (by decide)
  change (stackPtr s-136).toNat = (stackPtr s).toNat-136 at hsp
  intro c hc a ha
  simp only [scratchComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim ha
  obtain ⟨i, hi, rfl⟩ := ha
  refine ⟨Stack.region s 136, by simp, ?_⟩
  apply memoryRegion_contains_add pre.stack.1 (len := 88) _ _ hi
  · rw [hsp]
    change (stackPtr s).toNat-136 ≤ (stackPtr s).toNat-136
    omega
  · rw [stack_region_end, hsp]
    have := (stack_bounds pre.stack).1
    omega

theorem scratch_agrees_trans {s t u : RamState} {base : BitVec 64}
    (h : AgreesExcept (scratchComponents base) s t)
    (h' : AgreesExcept (scratchComponents base) t u) :
    AgreesExcept (scratchComponents base) s u :=
  (h.trans h').mono (by simp)

theorem scratch_saved {s t : RamState} {base : BitVec 64}
    (h : AgreesExcept (scratchComponents base) s t)
    {c : BitVec 64} (hc : OffsetsApart 0 88 c 8) :
    memLoad t.external (base+c) 64 = memLoad s.external (base+c) 64 := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  apply h.memory
  intro d hd he
  simp only [scratchComponents, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact False.elim he
  obtain ⟨j, hj, he⟩ := he
  apply hc.ne base hj hi (by decide)
  change base+0#64+BitVec.ofNat 64 j = _
  rw [BitVec.add_zero]
  exact he.symm

end P256.Proofs.Field.Schoolbook
