import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Sec1.Parser.LengthTable

namespace K256.Proofs.Sec1.Parser

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Sec1.LIR K256.Proofs.Refine

def GuardRegisters (before after : Vector Value 53) : Prop :=
  ∀ i : Fin 53, i.val ∈ [2, 4, 5, 6, 7, 12, 13, 22, 39, 50, 51] → after[i] = before[i]

local macro "guard_regs" : tactic => `(tactic|
  (intro ⟨i, hi⟩ h
   simp only [List.mem_cons, List.not_mem_nil, or_false] at h
   rcases h with h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl))

theorem tagBlock {code : CodeMap} {args : Vector Value 53} {mem : Ram} {ptr : BitVec 64}
    (rsi : Value.get 64 args[6] = ptr) (read : LoadOk mem ptr 1) :
    let t := memLoad mem ptr 8
    ∃ next : Vector Value 53, program.runBlock (dialect code) ⟨.l1063a7, args, mem⟩ =
        .jump ⟨if validTag t then .l1063c4 else .l106560, next, mem⟩ ∧
      next[1] = ⟨64, t.setWidth 64⟩ ∧ GuardRegisters args next := by
  dsimp only
  have cf (t : BitVec 8) : (cmpSpec (t.setWidth 64) 6).CF = decide ((t.setWidth 64).toNat < 6) := rfl
  by_cases valid : validTag (memLoad mem ptr 8)
  all_goals
    refine ⟨?next, ?eval, ?tag, ?keeps⟩
    case eval =>
      cfg_eval
      simp only [rsi, read, ite_true, setWidth_mergeGPR8]
      simp only [cf, decide_eq_true_eq, cmpSpec_ZF, Bool.not_eq_true', beq_eq_false_iff_ne,
        ne_eq, tagMask, valid, not_true_eq_false, not_false_eq_true, ↓reduceIte]
      first | rw [ite_eq_left valid] | rw [ite_eq_right valid]
    case tag => rfl
    case keeps => guard_regs

theorem lengthBlock {code : CodeMap} {args : Vector Value 53} {mem : Ram} {t : BitVec 8}
    {len : BitVec 64} (rcx : Value.get 64 args[1] = t.setWidth 64)
    (rdx : Value.get 64 args[2] = len) (valid : validTag t)
    (loaded : ∀ x ∈ K256.Spec.Program.Extracted.programImage, mem[x.1]? = some x.2) :
    let expected := lengthTable.get ⟨t.toNat, validTag_lt valid⟩
    ∃ next : Vector Value 53, program.runBlock (dialect code) ⟨.l1063c4, args, mem⟩ =
        .jump ⟨if len = expected then .l1063d2 else .l106560, next, mem⟩ ∧
      GuardRegisters args next := by
  have hx := lengthTable_load loaded ⟨t.toNat, validTag_lt valid⟩
  have read : LoadOk mem (wordAddr 0x202548 64 t.toNat) 8 := ⟨hx.1.low, hx.1.present⟩
  have table : memLoad mem (wordAddr 0x202548 64 t.toNat) 64 =
      lengthTable.get ⟨t.toNat, validTag_lt valid⟩ := hx.2
  dsimp only
  refine ⟨?next, ?eval, ?keeps⟩
  case eval =>
    cfg_eval
    simp only [rcx, rdx, lengthTable_address, BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64),
      read, table, cmpSpec_ZF, Bool.not_eq_true', beq_eq_false_iff_ne, ite_true]
    split
    · rename_i h
      rw [ite_eq_right h]
    · rename_i h
      rw [ite_eq_left (Classical.not_not.mp h)]
  case keeps => guard_regs

end K256.Proofs.Sec1.Parser
