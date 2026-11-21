import K256.Proofs.Generate.Generator.Affine.State
import K256.Proofs.Generate.LIR.Functions1
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Affine

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator.Affine
open Standards.SECG.ECC

def childWrites (sp : Word) : List MemoryRegion :=
  [⟨(sp - 296).toNat, 56⟩, ⟨(sp + 144).toNat, 81⟩]

def childResult (choice : Bool) (a : Registers) (m : Ram) (sp : Word) (o : Output Value Ram Reg.count) : Prop :=
  o.tag = some ⟨64, 0x10ee65⟩ ∧ o.values[4] = ⟨64, sp - 232⟩ ∧
  (∀ i : Fin Reg.count, i.val ∈ [3, 14, 22, 39, 50, 51] → o.values[i] = a[i]) ∧
  RamWriteFrame m o.store (childWrites sp) ∧
  (∀ i < 5, memLoad o.store (sp + 144 + BitVec.ofNat 64 (8*i)) 64 =
    memLoad m ((if choice then sp - 144 else sp - 232) + BitVec.ofNat 64 (8*i)) 64)

private theorem selectMask (x y : Word) :
    ((y ^^^ x) &&& (0xffffffffffffffff : Word)) ^^^ x = y := by
  change ((y ^^^ x) &&& BitVec.allOnes 64) ^^^ x = y
  rw [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem selectZero (x y : Word) :
    ((y ^^^ x) &&& (0 : Word)) ^^^ x = x := by
  change ((y ^^^ x) &&& 0#64) ^^^ x = x
  simp only [BitVec.and_zero, BitVec.zero_xor]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem checkedSelection {m : Ram} {a : Registers} {sp : Word}
    (rsp : a[4].get 64 = sp - 240) (rdx : a[2].get 64 = sp - 144)
    (rsi : a[6].get 64 = sp - 232) (rdi : a[7].get 64 = sp + 144)
    {choice : Bool} (rcx : a[1].get 64 = (if choice then 1 else 0)) {bx r14 : Word}
    (hbx : a[3] = ⟨64, bx⟩) (h14 : a[14] = ⟨64, r14⟩)
    (scratch : Writable Extracted.programImage m (sp - 296) 64)
    (source : Readable m (sp - 144) 81) (defaultSource : Readable m (sp - 232) 81)
    (dest : Writable Extracted.programImage m (sp + 144) 81)
    (ret : memLoad m (sp - 240) 64 = 0x10ee65)
    (room : 296 ≤ sp.toNat) (high : sp.toNat + 232 ≤ 2^32) :
    Onward lifted Extracted.programImage (fun _ => False)
      (ReturnOf (childResult choice a m sp))
      (program.runBlock (dialect Extracted.programImage) ⟨.l120470, a, m⟩) := by
  have lo := scratch.readable.low
  have loSrc := source.low
  have loDefault := defaultSource.low
  have loDest := dest.readable.low
  cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte] at rcx ⊢
  all_goals
    cfg_eval [rsp, rdx, rsi, rdi, rcx]
    repeat' (refine Onward.guard ?_ ?_; rotate_left)
    all_goals
      try (first | slot_guard using code_l120470 |
        (constructor
         · slot_guard using code_l120470
         · refine_norm [ret]; decide))
    apply Onward.returned
    apply ReturnOf.intro
    unfold childResult
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine_norm [ret]
    · rfl
    · rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | rfl
        | change _ = a[3]; refine_norm [hbx]
        | change _ = a[14]; refine_norm [h14]
    · unfold childWrites
      repeat' apply RamWriteFrame.memStore
      · exact RamWriteFrame.refl _ _
      all_goals
        first
        | refine ⟨_, List.mem_cons_self, ?_⟩
          change (sp - 296).toNat ≤ _ ∧ _ ≤ (sp - 296).toNat + 56 ∧ _
          bv_omega
        | refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
          change (sp + 144).toNat ≤ _ ∧ _ ≤ (sp + 144).toNat + 81 ∧ _
          bv_omega
    · intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [Bool.false_eq_true, ↓reduceIte];
         refine_norm [selectMask, Nat.reduceMul, BitVec.reduceOfNat]; try first | rfl | exact selectZero _ _)

theorem runSelection {m : Ram} {a : Registers} {sp : Word}
    (rsp : a[4].get 64 = sp - 240) (rdx : a[2].get 64 = sp - 144)
    (rsi : a[6].get 64 = sp - 232) (rdi : a[7].get 64 = sp + 144)
    {choice : Bool} (rcx : a[1].get 64 = (if choice then 1 else 0)) {bx r14 : Word}
    (hbx : a[3] = ⟨64, bx⟩) (h14 : a[14] = ⟨64, r14⟩)
    (scratch : Writable Extracted.programImage m (sp - 296) 64)
    (source : Readable m (sp - 144) 81) (defaultSource : Readable m (sp - 232) 81)
    (dest : Writable Extracted.programImage m (sp + 144) 81)
    (ret : memLoad m (sp - 240) 64 = 0x10ee65)
    (room : 296 ≤ sp.toNat) (high : sp.toNat + 232 ≤ 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l120470, a, m⟩, []⟩ out ∧
      childResult choice a m sp out := by
  have post := checkedSelection rsp rdx rsi rdi rcx hbx h14 scratch source defaultSource dest ret room high
  generalize step : program.runBlock (dialect Extracted.programImage) ⟨.l120470, a, m⟩ = transfer at post
  cases transfer with
  | returned out => exact ⟨out, .done (by simp only [Program.step, step, Transfer.next]), post⟩
  | jump _ =>
      obtain ⟨_, _, h⟩ := post
      exact h.elim
  | call _ _ => exact False.elim post
  | stuck => exact False.elim post

end K256.Proofs.Verify.Core.Affine
