import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Run.Iteration
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open SafeGcd.Batch (Words)

variable {a b : Registers} {m p : Ram} {sp : Word} {z : Fin modulus} {w : Vector Word 4}

private theorem exitRows {s : Words} (rows : Rows b p sp s) :
    ∃ c, Reaches .l1093f9 b p .l108f97 c p ∧ Controls b c ∧ Rows c p sp s := by
  refine ⟨?_, ?reach, ?post⟩
  case reach =>
    refine .step ?_ (.refl _)
    change (program.runBlock _ _).next _ _ = _
    generate_block []
    rfl
  case post =>
    constructor
    · intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    · exact ⟨rows.rsp, rows.scratch, rows.delta, rows.u, rows.v, rows.q, rows.r⟩

theorem runWords {s : Words} {n : Nat} (pos : 0 < n) (limit : n ≤ 62)
    (inner : Inner b p sp s n) (low : 736 ≤ sp.toNat) (high : sp.toNat + 129 ≤ 2^32)
    (stack : Writable Extracted.programImage p (base sp + 8) 104) :
    ∃ c q, Reaches .l1092a0 b p .l108f97 c q ∧ Controls b c ∧
      RamWriteFrame p q (work sp) ∧ Rows c q sp (SafeGcd.Batch.run n s) := by
  induction n generalizing b p s with
  | zero => omega
  | succ n ih =>
    obtain ⟨c, q, reach, kept, frame, next, rows⟩ := iteration (by omega) inner low high stack
    cases n with
    | zero =>
      obtain ⟨d, exit, keepExit, out⟩ := exitRows rows
      exact ⟨d, q, reach.trans exit, fun i hi => (keepExit i hi).trans (kept i hi), frame, out⟩
    | succ n =>
      obtain ⟨d, r, rest, keepRest, writes, out⟩ :=
        ih (by omega) (by omega) next (stack.of_frame frame)
      exact ⟨d, r, reach.trans rest, fun i hi => (keepRest i hi).trans (kept i hi),
        frame.trans writes (fun x hx => ⟨x, hx, Nat.le_refl _, Nat.le_refl _⟩), out⟩

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
