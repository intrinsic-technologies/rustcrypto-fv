import K256.Proofs.Verify.Hash.Compression.Groups.Boundaries

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Values

private def stable : Values.Op → Prop
  | .store32 off _ | .addStack32 off _ => 24 ≠ off ∧ 28 ≠ off
  | .store64 off _ => 24 ≠ off ∧ 28 ≠ off ∧ 24 ≠ off + 4 ∧ 28 ≠ off + 4
  | .mov32 d _ | .mov64 d _ | .binary32 _ d _ | .not32 d | .rol32 d _
    | .shr32 d _ | .lea32 d _ _ _ _ | .bswap32 d => 4 ≠ d

private instance (op : Values.Op) : Decidable (stable op) := by
  cases op <;> simp only [stable] <;> infer_instance

private instance (op : Values.Op) : Decidable op.validSpills := by
  cases op <;> simp only [Values.Op.validSpills, ValidSpill] <;> infer_instance

def chainSafe (ops : List Values.Op) : Bool :=
  ops.all (fun op => decide (stable op ∧ op.validSpills))

private theorem stable_step {op : Values.Op} (ok : stable op) (ctx : ValueContext) (s : Compression.Values)
    (h : s.regs 4 = ctx.stackPointer ∧ spilledInput ctx s) :
    (op.eval ctx s).regs 4 = ctx.stackPointer ∧ spilledInput ctx (op.eval ctx s) := by
  cases op <;> simp only [stable] at ok <;>
    (try obtain ⟨o1, o2, o3, o4⟩ := ok) <;> (try obtain ⟨o1, o2⟩ := ok) <;>
    simpa only [spilledInput, Values.Op.eval, writeReg, write32, write64, *, ↓reduceIte] using h

theorem chainSafe_pointers {xs} (ok : chainSafe xs) (ctx : ValueContext) (s : Compression.Values)
    (h : s.regs 4 = ctx.stackPointer ∧ spilledInput ctx s) :
    (run ctx xs s).regs 4 = ctx.stackPointer ∧ spilledInput ctx (run ctx xs s) := by
  induction xs generalizing s with
  | nil => exact h
  | cons op xs ih =>
    change (_ && chainSafe xs) = true at ok
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
    exact ih tail _ (stable_step (of_decide_eq_true head).1 ctx s h)

theorem GroupStep.chain {n k j : Nat}
    {start : Block Lift.Op Label signature Reg.count n}
    {middle : Block Lift.Op Label signature Reg.count k}
    {last : Block Lift.Op Label signature Reg.count j}
    {xs ys : List Values.Op} {before between after}
    (left : GroupStep start middle xs before between spilledInput)
    (right : GroupStep middle last ys between after spilledInput)
    (ok : chainSafe xs) :
    GroupStep start last (xs ++ ys) before after spilledInput :=
  left.append right (fun op h => (of_decide_eq_true (List.all_eq_true.mp ok op h)).2)
    (fun ctx s sp ptr => chainSafe_pointers ok ctx s ⟨sp, ptr⟩)

end K256.Proofs.Verify.Hash.Compression
