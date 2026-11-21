import K256.Proofs.ParseSignature.Contract
import K256.Proofs.LIR.Fn103ac0.Frame
import K256.Proofs.ParseSignature.Scalar
import K256.Proofs.ParseSignature.Pair.First
import K256.Proofs.ParseSignature.Pair.Second
import K256.Proofs.ParseSignature.Pair.Decode
import K256.Proofs.ParseSignature.Pair.Zero
import K256.Proofs.ParseSignature.Pair.Finish

namespace K256.Proofs.ParseSignature

open Standards.SECG.DomainParameters K256.Spec K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

private theorem forgetPairSlots {code : CodeMap} {fr : Activation} {args : Values Value Reg.count} {mem : Ram}
    (active : Pair.Active code fr true args mem) : Pair.Active code fr false args mem := by
  refine ⟨?_, active.writes, active.widths⟩
  have h := active.atoms
  change Atom.All code args mem (LIR.Fn103ac0.frameAt .l103b80 fr ++
    LIR.Fn103ac0.frameInfo.callSlotAtoms LIR.Fn103ac0.frameInfo.callSlots fr) at h
  exact ((Atom.all_append _ _).mp h).1

theorem decodePair_call {code : CodeMap} (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (hr : Readable fr.original fr.rsi 64)
    (hw : Writable code fr.original fr.rdi 72)
    (hin : Outside [callStack fr] fr.rsi 64) (hout : Outside [callStack fr] fr.rdi 72) :
    Call code .l103ac0 LIR.Fn103ac0.frameInfo fr [buffer fr.rdi 72] fun out =>
      let r := scalarValue fr.original fr.rsi
      let s := scalarValue fr.original (fr.rsi + 32)
      if 0 < r ∧ r < Secp256k1.domain.n ∧ 0 < s ∧ s < Secp256k1.domain.n then
        memLoad out.store fr.rdi 64 = 0 ∧
          scalarLimbsAt out.store (fr.rdi + 8) fr.original fr.rsi ∧
          scalarLimbsAt out.store (fr.rdi + 40) fr.original (fr.rsi + 32)
      else memLoad out.store fr.rdi 64 = 1 ∧ memLoad out.store (fr.rdi + 8) 64 = 0 := by
  intro args entry
  let r := scalarValue fr.original fr.rsi
  let s := scalarValue fr.original (fr.rsi + 32)
  let valid := 0 < r ∧ r < Secp256k1.domain.n ∧ 0 < s ∧ s < Secp256k1.domain.n
  suffices path : ∃ regs mem,
      Pair.reaches code .l103ac0 args fr.original (if valid then .l103c6a else .l103c4d) regs mem ∧
      Pair.Active code fr false regs mem ∧
      (valid → scalarLimbsAt mem (Pair.sp fr + 104) fr.original fr.rsi ∧
        scalarLimbsAt mem (Pair.sp fr + 136) fr.original (fr.rsi + 32)) by
    obtain ⟨regs, mem, reached, active, limbs⟩ := path
    obtain ⟨out, run, post⟩ :=
      Pair.finishPair hcode fr regs mem (decide valid) active hw hout (fun h => limbs (of_decide_eq_true h))
    refine ⟨out, Program.Exec.of_sem (reached.exec ?_), ?_⟩
    · have label : (if decide valid then LIR.Label.l103c6a else .l103c4d) =
          (if valid then .l103c6a else .l103c4d) := by simp
      exact Eq.mp (congrArg (fun l => (LIR.program.sem (dialect code)).Exec
        ⟨⟨l, regs, mem⟩, []⟩ out) label) run.sem
    · change _ ∧ _ ∧ _ ∧ _ ∧ (if valid then _ else _)
      by_cases hv : valid <;> simpa [hv] using post
  obtain ⟨rargs, rmem, callR, entryR⟩ := Pair.firstScalarEntry hcode fr args entry hr hin
  obtain ⟨a, m, runR, activeR, limbsR, _⟩ :=
    Pair.runScalar hcode fr args fr.original .l103ac0 .l103b07 .l103b12 0x103b07 fr.rsi rargs rmem
      (List.Mem.head _) callR entryR
  by_cases hrange : r < Secp256k1.domain.n
  · rw [ite_eq_left hrange] at runR
    obtain ⟨sargs, smem, callS, entryS, keepR⟩ :=
      Pair.secondScalarEntry hcode fr a m activeR hr hin (limbsR hrange)
    obtain ⟨b, n, runS, activeS, limbsS, savedR⟩ :=
      Pair.runScalar hcode fr a m .l103b12 .l103b75 .l103b80 0x103b75 (fr.rsi + 32) sargs smem
        (List.Mem.tail _ (List.Mem.head _)) callS entryS
    by_cases hsrange : s < Secp256k1.domain.n
    · rw [ite_eq_left hsrange] at runS
      obtain ⟨c, t, zero, active, limbs⟩ :=
        Pair.checkNonzero hcode fr b n (forgetPairSlots activeS) (savedR keepR) (limbsS hsrange)
      have valid_iff : valid ↔ 0 < r ∧ 0 < s :=
        ⟨fun h => ⟨h.1, h.2.2.1⟩, fun h => ⟨h.1, hrange, h.2, hsrange⟩⟩
      have target : (if 0 < r ∧ 0 < s then LIR.Label.l103c6a else .l103c4d) =
          (if valid then .l103c6a else .l103c4d) := by
        simp only [valid, hrange, hsrange, true_and, and_true]
      rw [target] at zero
      exact ⟨c, t, (runR.trans runS).trans zero, active, fun h => limbs (valid_iff.mp h)⟩
    · have invalid : ¬ valid := fun h => hsrange h.2.2.2
      rw [ite_eq_right hsrange] at runS
      simp only [ite_eq_right invalid]
      exact ⟨b, n, runR.trans runS, forgetPairSlots activeS, fun h => (invalid h).elim⟩
  · have invalid : ¬ valid := fun h => hrange h.2.1
    rw [ite_eq_right hrange] at runR
    simp only [ite_eq_right invalid]
    exact ⟨a, m, runR, forgetPairSlots activeR, fun h => (invalid h).elim⟩

end K256.Proofs.ParseSignature
