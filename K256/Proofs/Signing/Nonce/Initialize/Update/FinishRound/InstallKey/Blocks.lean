import K256.Proofs.Signing.Nonce.Initialize.Update.FinishRound.InstallKey.Memory
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

private theorem callAfterKeyCopy {a : Verify.Core.Registers} {m : Ram} {rsp : BitVec 64}
    (stack : a[4] = ⟨64, rsp⟩) (slot : Writable Extracted.programImage m (rsp - 8) 8) :
    program.runBlock (dialect Extracted.programImage) ⟨.l10494c, a, m⟩ =
      .call ⟨.l104970, a.set 4 ⟨64, rsp - 8⟩, memStore m (rsp - 8) (0x104951 : BitVec 64)⟩
        (Verify.resumeAt .l104951 0x104951) := by
  have stackBits : a[4].get 64 = rsp := congrArg (Value.get 64) stack
  cfg_eval [stackBits]
  rw [ite_eq_left (by slot_guard using code_l10494c)]
  congr 2
  apply (show ∀ {u v : Verify.Core.Registers}, (∀ j : Fin Reg.count, u[j.val] = v[j.val]) → u = v
    from fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
  intro j
  change Fin 53 at j
  finite_cases j <;> rw [Vector.getElem_set] <;> rfl

set_option maxHeartbeats 300000 in
theorem keyCallPath {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (second : Bool) (env : Environment fr input)
    (roundOk : second = true → seeded input = true)
    (live : Live (keyAt second input) fr a m state) (slots : seeded input = true → Slots fr m)
    (widths : ParseSignature.ArgumentWidths a) :
    ∃ b, (program.sem (dialect Extracted.programImage)).Reaches ⟨⟨keyAt second input, a, m⟩, []⟩
      ⟨⟨.l104970, b, keyCallMemory m fr second input⟩, [Verify.resumeAt (resume second input) (valueReturn second input)]⟩ ∧
      ParseSignature.ArgumentWidths b ∧ b[4] = ⟨64, sp fr - 8⟩ ∧ b[7] = ⟨64, fr.rdi⟩ ∧
      ((!second && seeded input) = true → b[3] = ⟨64, fr.rdi⟩) ∧
      (∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      b[3].width = 64 := by
  have stk := env.stack.of_frame live.writes
  have dest := env.writable.of_frame live.writes
  have depth := env.depth
  have low := stk.readable.low
  have destLow := dest.readable.low
  have bxWidth : a[3].width = 64 := live.savedWidths 3 (by decide)
  have atoms := live.atoms
  by_cases firstSeeded : (!second && seeded input) = true
  · have first : second = false := by cases second <;> simp_all only [Bool.not_true, Bool.false_and, Bool.false_eq_true]
    subst second
    have hasSeed : seeded input = true := by simpa only [Bool.not_false, Bool.true_and] using firstSeeded
    have dstLoad := (slots hasSeed).state
    have label : keyAt false input = .l10435b := by
      unfold keyAt
      rw [ite_eq_right Bool.false_ne_true, ite_eq_left hasSeed]
    rw [label] at atoms ⊢
    simp only [Fn103f30.frameAt] at atoms
    have rsp : a[4].get 64 = sp fr := congrArg (Value.get 64) atoms.1
    simp only [digestPtr, keyCallMemory, valueReturn, resume, hasSeed, Bool.not_false,
      Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    suffices ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10435b, a, m⟩ =
        .call ⟨.l104970, b, memStore (keyCopy m (sp fr + 16) fr.rdi) (sp fr - 8) (0x10438b : BitVec 64)⟩
          (Verify.resumeAt .l10438b 0x10438b) ∧
        ParseSignature.ArgumentWidths b ∧ b[4] = ⟨64, sp fr - 8⟩ ∧ b[7] = ⟨64, fr.rdi⟩ ∧
        b[3] = ⟨64, fr.rdi⟩ ∧
        (∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15,22,39,50,51] → b[i] = a[i]) by
      obtain ⟨b, run, bw, stack, dst, bx, keep⟩ := this
      exact ⟨b, .single (congrArg (Transfer.next _ []) run), bw, stack, dst, fun _ => bx,
        keep, congrArg Value.width bx⟩
    refine ⟨?_, ?run, ?post⟩
    case run =>
      cfg_eval [rsp, dstLoad]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10435b)
      simp only [keyCopy, BitVec.add_assoc, BitVec.reduceAdd]
      rfl
    case post =>
      refine ⟨?_, rfl, rfl, rfl, ?_⟩
      · intro ⟨i, _⟩ hi
        simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | rfl | exact widths 6 (by decide) | exact widths 2 (by decide) |
            exact widths 8 (by decide) | exact widths 9 (by decide)
      · intro ⟨i, _⟩ hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · let copied := keyCopy m (digestPtr fr second) fr.rdi
    have copiedSlot : Writable Extracted.programImage copied (sp fr - 8) 8 := by
      have slot : Writable Extracted.programImage m (sp fr - 8) 8 := by slot_state region
      dsimp only [copied, keyCopy]
      repeat' apply Writable.memStore
      exact slot
    have next : ∃ c, program.runBlock (dialect Extracted.programImage) ⟨keyAt second input, a, m⟩ =
        .jump ⟨.l10494c, c, copied⟩ ∧ ParseSignature.ArgumentWidths c ∧
        c[4] = ⟨64, sp fr⟩ ∧ c[7] = ⟨64,fr.rdi⟩ ∧ c[3] = a[3] ∧
        (∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15,22,39,50,51] → c[i] = a[i]) := by
      cases second
      case' false =>
        have noSeed : seeded input ≠ true := by
          simpa only [Bool.not_false, Bool.true_and] using firstSeeded
        have label : keyAt false input = .l1046f1 := by
          unfold keyAt
          rw [ite_eq_right Bool.false_ne_true, ite_eq_right noSeed]
        rw [label] at atoms ⊢
      case' true =>
        have dstLoad := (slots (roundOk rfl)).state
        have label : keyAt true input = .l104918 := rfl
        rw [label] at atoms ⊢
      all_goals
        simp only [Fn103f30.frameAt, Fn103f30.frameAtG5, Atom.All, Atom.Holds] at atoms
        have rsp : a[4].get 64 = sp fr := congrArg (Value.get 64) atoms.1
        refine ⟨?_, ?run, ?post⟩
        case run =>
          first
          | change program.runBlock _ ⟨.l1046f1, a, m⟩ = _
            have dst : a[5].get 64 = fr.rdi := congrArg (Value.get 64) atoms.2.2.1
            cfg_eval [rsp, dst]
            repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1046f1)
          | change program.runBlock _ ⟨.l104918, a, m⟩ = _
            cfg_eval [rsp, dstLoad]
            repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l104918)
          simp only [copied, digestPtr, Bool.false_eq_true, ↓reduceIte, keyCopy,
            BitVec.add_assoc, BitVec.reduceAdd]
          rfl
        case post =>
          refine ⟨?_, atoms.1, rfl, rfl, ?_⟩
          · intro ⟨i, _⟩ hi
            simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
              first | rfl | exact widths 6 (by decide) | exact widths 2 (by decide) |
                exact widths 8 (by decide) | exact widths 9 (by decide)
          · intro ⟨i, _⟩ hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    obtain ⟨c, jump, cw, stack, dst, bx, keep⟩ := next
    let b := c.set 4 ⟨64, sp fr - 8⟩
    refine ⟨b, ?_, ?_, ?_, ?_, fun h => (firstSeeded h).elim, ?_, ?_⟩
    · simp only [keyCallMemory, valueReturn, resume, ite_eq_right firstSeeded]
      refine .step (congrArg (Transfer.next _ []) jump) (.step ?_ (.refl _))
      exact congrArg (Transfer.next _ []) (callAfterKeyCopy stack copiedSlot)
    · intro i hi
      have ne : i.val ≠ 4 := by
        simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
        omega
      simpa only [b, Fin.getElem_fin, Vector.getElem_set, ite_eq_right (Ne.symm ne)] using cw i hi
    · simp only [b, Vector.getElem_set, ↓reduceIte]
    · simpa only [b, Fin.getElem_fin, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using dst
    · intro i hi
      have ne : i.val ≠ 4 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        omega
      simpa only [b, Fin.getElem_fin, Vector.getElem_set, ite_eq_right (Ne.symm ne)] using keep i hi
    · simpa only [b, Fin.getElem_fin, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte, bx] using bxWidth

end K256.Proofs.Signing.Nonce.Initialize.Update
