import P256.Proofs.Verifying.Combination.Prologue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Spec.Program.Routines

def localRegion (s : RamState) (offset len : Nat) : MemoryRegion :=
  ⟨(stackPtr s - BitVec.ofNat 64 offset).toNat, len⟩

theorem localRegion_sub [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {offset len : Nat}
    (ho : offset ≤ 8808) (hl : len ≤ offset + 8) :
    ∀ a, (localRegion s offset len).Contains a → (Stack.region s 8808).Contains a := by
  have hb := stack_bounds pre.stack
  intro a ha
  change (stackPtr s - BitVec.ofNat 64 offset).toNat ≤ a ∧
    a < (stackPtr s - BitVec.ofNat 64 offset).toNat + len at ha
  rw [stack_sub_toNat pre.stack ho] at ha
  change (stackPtr s).toNat - 8808 ≤ a ∧ a < (Stack.region s 8808).start + (Stack.region s 8808).size
  rw [stack_region_end]
  constructor <;> omega

theorem localRegion_bounded [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {offset len : Nat}
    (ho : offset ≤ 8808) (hl : len ≤ offset + 8) : (localRegion s offset len).Bounded := by
  have hb := stack_bounds pre.stack
  change (stackPtr s - BitVec.ofNat 64 offset).toNat + len < 2^32
  rw [stack_sub_toNat pre.stack ho]
  omega

theorem localRegion_allocated [Bindings] {s t : RamState} {boundary : ReturnBoundary} {so : BitVec 64}
    (pre : Pre s boundary) (state : State s t so)
    {offset len : Nat} (ho : offset ≤ 8808) (hl : len ≤ offset + 8) :
    (localRegion s offset len).Allocated t.external := by
  intro a ha
  exact Option.isSome_iff_exists.mp (state.allocated a
    (Option.isSome_iff_exists.mpr (pre.stack.2.1 a (localRegion_sub pre ho hl a.toNat ha))))

theorem localRegion_avoids [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {offset len : Nat}
    (ho : offset ≤ 8808) (hl : len ≤ offset + 8) :
    (localRegion s offset len).Avoids (fun a => InProgram a ∨ InPageTables a) := by
  intro a ha
  exact pre.avoids _ (by simp) a (localRegion_sub pre ho hl a.toNat ha)

theorem localRegion_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) {a b n m : Nat}
    (ha : a ≤ 8808) (hb : b ≤ 8808) (apart : a + m ≤ b ∨ b + n ≤ a) :
    (localRegion s a n).Disjoint (localRegion s b m) := by
  have bounds := stack_bounds pre.stack
  intro x hx hy
  change (stackPtr s - BitVec.ofNat 64 a).toNat ≤ x ∧
    x < (stackPtr s - BitVec.ofNat 64 a).toNat + n at hx
  change (stackPtr s - BitVec.ofNat 64 b).toNat ≤ x ∧
    x < (stackPtr s - BitVec.ofNat 64 b).toNat + m at hy
  rw [stack_sub_toNat pre.stack ha] at hx
  rw [stack_sub_toNat pre.stack hb] at hy
  omega

theorem localRegion_stack_disjoint [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : State s t 6560)
    {offset len reserve : Nat} (ho : offset ≤ 6552) :
    (localRegion s offset len).Disjoint (Stack.region t reserve) := by
  have bounds := stack_bounds pre.stack
  intro a ha hb
  change (stackPtr s - BitVec.ofNat 64 offset).toNat ≤ a ∧
    a < (stackPtr s - BitVec.ofNat 64 offset).toNat + len at ha
  rw [stack_sub_toNat pre.stack (by omega)] at ha
  change (stackPtr t).toNat - reserve ≤ a ∧
    a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
  rw [stack_region_end, state.rsp] at hb
  rw [show (stackPtr s - 6560).toNat = (stackPtr s).toNat - 6560 from
    stack_sub_toNat pre.stack (offset := 6560) (by decide)] at hb
  omega

end P256.Proofs.Verifying.Combination
