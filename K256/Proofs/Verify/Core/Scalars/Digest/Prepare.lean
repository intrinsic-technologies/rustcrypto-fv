import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Verify.Core.Scalars.State

namespace K256.Proofs.Verify.Core.Digest

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def stage (m : Ram) (sp : BitVec 64) : Ram :=
  let w := memStore m (sp + 32) (memLoad m (sp + 160) 64)
  let w := memStore w (sp + 24) (memLoad m (sp + 152) 64)
  let w := memStore w (sp + 16) (memLoad m (sp + 144) 64)
  let w := memStore w (sp + 8) (memLoad m (sp + 136) 64)
  memStore w (sp - 8) (0x10518b : BitVec 64)

theorem stagedWords {m : Ram} {sp : BitVec 64} {v : Vector (BitVec 64) 4}
    (words : WordsAt m (sp + 136) 64 v) : WordsAt (stage m sp) (sp + 8) 64 v := by
  intro i hi
  rw [← words i hi]
  obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals simp (disch := store_disch) only [stage, wordAddr, Nat.reduceDiv, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
    memLoad_memStore_same, memLoad_memStore_of_rangeApart]

def resume : StackFrame Value Label signature Reg.count :=
  ⟨.l10518b, #v[], rfl, some ⟨64, 0x10518b⟩⟩

set_option maxRecDepth 4096 in
theorem prepare (a : Registers) (m : Ram) (sp : BitVec 64)
    (rsp : a[4].get 64 = sp) (stack : Writable Extracted.programImage m (sp - 8) 176) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l105145,a,m⟩ =
        .call ⟨.l109f80,b,stage m sp⟩ resume ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[6] = ⟨64, sp + 8⟩ ∧ b[7] = ⟨64, sp + 352⟩ ∧
      b[1].width = 64 ∧
      ∀ i : Fin Reg.count, i.val ∈ [2,3,5,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?b, ?step, ?regs⟩
  case step =>
    cfg_eval [rsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l105145)
    simp (disch := store_disch) only [stage, memLoad_memStore_of_rangeApart] <;> rfl
  case regs =>
    refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro ⟨i,_⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Verify.Core.Digest
