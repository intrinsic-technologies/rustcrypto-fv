import K256.Proofs.ParseSignature.Pair.Nonzero.Prepare
import K256.Proofs.ParseSignature.Pair.Nonzero.Branch
import K256.Proofs.ParseSignature.ScalarValue

namespace K256.Proofs.ParseSignature.Pair

open Standards.SECG.DomainParameters K256.Proofs.Common X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

private theorem checkOne {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (second : Bool)
    (active : Active code fr false args mem)
    (r : scalarLimbsAt mem (sp fr + 104) fr.original fr.rsi)
    (s : scalarLimbsAt mem (sp fr + (if second then 136 else 16)) fr.original (fr.rsi + 32)) :
    let src := if second then fr.rsi + 32 else fr.rsi
    ∃ next after, reaches code (if second then .l103bff else .l103b80) args mem
        (if scalarValue fr.original src = 0 then .l103c4d
         else if second then .l103c6a else .l103bff) next after ∧
      Active code fr false next after ∧ pairLimbs fr after := by
  dsimp only
  let src := if second then fr.rsi + 32 else fr.rsi
  let ret : BitVec 64 := if second then 0x103c3f else 0x103bf1
  obtain ⟨regs, pushed, call, caller, limbs, zeros, entry, di, si, dx, cx⟩ :=
    prepareZeroCompare hcode fr args mem second active r s
  let child := zeroChild fr regs pushed ret
  have h := caller.atoms
  change Atom.All code args pushed (Fn103ac0.frameAt .l103b80 fr) at h
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, stack, room, _, _⟩ := h
  change Writable code pushed (fr.rsp - 560) 560 at stack
  change fr.low.toNat + 560 ≤ fr.rsp.toNat at room
  have readable (off : BitVec 64) (hoff : off = 8 ∨ off = 104 ∨ off = 136) :
      Readable pushed (sp fr + off) 32 := by
    apply stack.readable.sub
    all_goals rcases hoff with rfl | rfl | rfl <;> unfold sp <;> bv_omega
  have readL : Readable pushed child.rdi 32 := by
    rw [show child.rdi = _ from di]
    exact readable _ (by cases second <;> simp)
  have readR : Readable pushed child.rdx 32 := by
    rw [show child.rdx = _ from dx]
    exact readable 8 (Or.inl rfl)
  obtain ⟨out, exec, tag, done, _, widths, unchanged, eqByte, binary⟩ :=
    ctEq_call hcode child si cx readL readR regs entry
  have merged := reachesOfCall call exec tag
  have live : Active code fr false out.values out.store := by
    have callerAfter : Active code fr false args out.store := by
      rwa [show out.store = pushed from unchanged]
    exact activeOfZeroReturn callerAfter done widths
  have saved : pairLimbs fr out.store := by rwa [show out.store = pushed from unchanged]
  have words : scalarLimbsAt pushed child.rdi fr.original src := by
    rw [show child.rdi = _ from di]
    cases second
    · exact limbs.1
    · exact limbs.2
  have eqZero : out.values[0].get 8 = 1 ↔ scalarValue fr.original src = 0 := by
    rw [eqByte, scalarValue_eq_zero_iff]
    change (∀ i < 4, memLoad pushed (wordAddr child.rdi 64 i) 64 =
      memLoad pushed (wordAddr child.rdx 64 i) 64) ↔ _
    rw [show child.rdx = _ from dx]
    constructor
    · intro he i hi
      exact (words i hi).symm.trans ((he i hi).trans (zeros i hi))
    · intro he i hi
      exact (words i hi).trans ((he i hi).trans (zeros i hi).symm)
  let zero := decide (scalarValue fr.original src = 0)
  have value : out.values[0].get 8 = if zero then 1 else 0 := by
    by_cases hz : scalarValue fr.original src = 0
    · simpa only [zero, hz, decide_true, ↓reduceIte] using eqZero.mpr hz
    · simpa only [zero, decide_eq_true_eq, hz, ↓reduceIte] using
        binary.resolve_right (fun one => hz (eqZero.mp one))
  obtain ⟨next, after, branch, finalState, preserved⟩ :=
    branchOnZero hcode fr out.values out.store second zero live saved value
  exact ⟨next, after, merged.trans (by simpa only [zero, decide_eq_true_eq] using branch),
    finalState, preserved⟩

theorem checkNonzero {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (active : Active code fr false args mem)
    (r : scalarLimbsAt mem (sp fr + 104) fr.original fr.rsi)
    (s : scalarLimbsAt mem (sp fr + 16) fr.original (fr.rsi + 32)) :
    let valid := 0 < scalarValue fr.original fr.rsi ∧ 0 < scalarValue fr.original (fr.rsi + 32)
    ∃ regs after, reaches code .l103b80 args mem (if valid then .l103c6a else .l103c4d) regs after ∧
      Active code fr false regs after ∧
      (valid → scalarLimbsAt after (sp fr + 104) fr.original fr.rsi ∧
        scalarLimbsAt after (sp fr + 136) fr.original (fr.rsi + 32)) := by
  dsimp only
  obtain ⟨a, m, first, live, limbs⟩ := checkOne hcode fr args mem false active r s
  by_cases hr : scalarValue fr.original fr.rsi = 0
  · simp only [Bool.false_eq_true, ↓reduceIte, hr, Nat.lt_irrefl, false_and] at first ⊢
    exact ⟨a, m, first, live, False.elim⟩
  · simp only [Bool.false_eq_true, ↓reduceIte, hr] at first
    obtain ⟨b, n, second, finalState, saved⟩ := checkOne hcode fr a m true live limbs.1 limbs.2
    refine ⟨b, n, first.trans ?_, finalState, fun _ => saved⟩
    by_cases hs : scalarValue fr.original (fr.rsi + 32) = 0
    · rw [ite_eq_right (by omega : ¬ (0 < scalarValue fr.original fr.rsi ∧ 0 < scalarValue fr.original (fr.rsi + 32)))]
      simpa only [↓reduceIte, hs] using second
    · have positive : 0 < scalarValue fr.original fr.rsi ∧ 0 < scalarValue fr.original (fr.rsi + 32) :=
        ⟨Nat.pos_of_ne_zero hr, Nat.pos_of_ne_zero hs⟩
      rw [ite_eq_left positive]
      simpa only [↓reduceIte, hs] using second

end K256.Proofs.ParseSignature.Pair
