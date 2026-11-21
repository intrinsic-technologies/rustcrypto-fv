import P256.Proofs.Verifying.Combination.PointNegativeFinish.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem negative_finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point selected : Projective} {u v k : Nat} {left : Bool}
    (pre : MultiPre s boundary tables digits)
    (state : DigitData s t tables digits p q u v k point left)
    (rip : t.RIP = 0x10f241) (r14 : t.regValue .r14 = stackPtr s-112#64)
    (source : ProjectiveAt t (stackPtr s-240#64) selected)
    (negY : MontgomeryAt t (stackPtr s-112#64) selected.negate.y) :
    ∃ fuel w, Advances boundary fuel t w ∧
      SelectedState s w tables digits p q u v k point selected.negate left := by
  have hp : NegativeFinish.Pre t := by
    refine ⟨rip, ?_, ?_, ?_, ?_⟩
    · change t.regValue .r14 = stackPtr t+296#64
      rw [r14, state.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    · intro offset bound
      exact stack_readable (frameOffset := 408) pre.toCalleePre state.toFrameState (by decide) bound
    · intro offset bound align
      change MemWritable t (stackPtr t+BitVec.ofNat 64 offset) 8
      rw [scalar_stack_address (frameOffset := 408) state.rsp (by decide) (by omega)]
      exact writable_of_grow (stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids (Stack.region s 1432) (by simp) a ha (.inr hp))
        (by omega) (by omega)) state.allocated
    · intro offset pc len bound codeBound
      exact stack_code (frameOffset := 408) pre.toCalleePre state.toFrameState (by decide) (by omega) codeBound
  obtain ⟨fuel, w, run, ready, _, effect⟩ :=
    NegativeFinish.correct boundary pre.outerBoundary t
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf241 NegativeFinish.bytes
        (by decide) (by decide +kernel)) hp
  have agrees := NegativeFinish.effect_frame effect
  have frame := NegativeFinish.after_effect pre.toCalleePre state.toFrameState ready agrees
  have kept {off len i : Nat} := NegativeFinish.kept (off := off) (len := len) (i := i)
    pre.toCalleePre state.toFrameState agrees
  have read (off : Nat) (ho : off ≤ 408)
      (hx : off+32 ≤ 144 ∨ 144+8 ≤ off) (hz : off+32 ≤ 80 ∨ 80+8 ≤ off) :
      memLoad w.external (stackPtr s-BitVec.ofNat 64 off) 64 =
        memLoad t.external (stackPtr s-BitVec.ofNat 64 off) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (kept ho (by omega) hx hz hi)
  have data : DigitData s w tables digits p q u v k point left := by
    refine ⟨⟨state.toMemory.of_frame pre frame,
      (agrees.read (n := 64) (r := 3) (by simp [NegativeFinish.components])).trans state.count,
      state.positive, state.bounded,
      (agrees.read (n := 64) (r := 15) (by simp [NegativeFinish.components])).trans state.scratch,
      state.value.of_bytes_eq (fun i hi => kept (off := 336) (len := 96) (by decide) (by decide) (by omega) (by omega) hi),
      (read 400 (by decide) (by decide) (by decide)).trans state.total,
      (read 384 (by decide) (by decide) (by decide)).trans state.tableBase,
      (read 392 (by decide) (by decide) (by decide)).trans state.output⟩,
      (agrees.read (n := 64) (r := 13) (by simp [NegativeFinish.components])).trans state.cursor,
      (agrees.read (n := 64) (r := 5) (by simp [NegativeFinish.components])).trans state.tableCursor,
      (agrees.read (n := 64) (r := 12) (by simp [NegativeFinish.components])).trans state.remaining,
      (read 376 (by decide) (by decide) (by decide)).trans state.savedCursor⟩
  have writes := effect.writes
  change _ ∧ _ ∧
    memLoad w.external (stackPtr t+288#64) 64 = memLoad t.external (stackPtr t+192#64) 64 ∧
    memLoad w.external (stackPtr t+280#64) 64 = memLoad t.external (stackPtr t+184#64) 64 ∧
    memLoad w.external (stackPtr t+272#64) 64 = memLoad t.external (stackPtr t+176#64) 64 ∧
    memLoad w.external (stackPtr t+264#64) 64 = memLoad t.external (stackPtr t+168#64) 64 ∧
    memLoad w.external (stackPtr t+352#64) 64 = memLoad t.external (stackPtr t+256#64) 64 ∧
    memLoad w.external (stackPtr t+344#64) 64 = memLoad t.external (stackPtr t+248#64) 64 ∧
    memLoad w.external (stackPtr t+336#64) 64 = memLoad t.external (stackPtr t+240#64) 64 ∧
    memLoad w.external (stackPtr t+328#64) 64 = memLoad t.external (stackPtr t+232#64) 64 at writes
  obtain ⟨_, _, x3, x2, x1, x0, z3, z2, z1, z0⟩ := writes
  have wordsX : ∀ j < 4,
      memLoad w.external (stackPtr s-144#64+BitVec.ofNat 64 (8*j)) 64 =
        memLoad t.external (stackPtr s-240#64+BitVec.ofNat 64 (8*j)) 64 := by
    intro j hj
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa [state.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc] using x0
    · simpa [state.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc] using x1
    · simpa [state.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc] using x2
    · simpa [state.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc] using x3
  have wordsZ : ∀ j < 4,
      memLoad w.external (stackPtr s-80#64+BitVec.ofNat 64 (8*j)) 64 =
        memLoad t.external (stackPtr s-176#64+BitVec.ofNat 64 (8*j)) 64 := by
    intro j hj
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa [state.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc] using z0
    · simpa [state.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc] using z1
    · simpa [state.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc] using z2
    · simpa [state.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc] using z3
  have valueX : MontgomeryAt w (stackPtr s-144#64) selected.x :=
    source.1.of_bytes_eq (NegativeFinish.copied_bytes pre.toCalleePre state.toFrameState frame
      (by decide) (by decide) (by decide) (by decide) wordsX)
  have sourceZ : MontgomeryAt t (stackPtr s-176#64) selected.z := by
    simpa [BitVec.sub_eq_add_neg, BitVec.add_assoc] using source.2.2
  have valueZ : MontgomeryAt w (stackPtr s-80#64) selected.z :=
    sourceZ.of_bytes_eq (NegativeFinish.copied_bytes pre.toCalleePre state.toFrameState frame
      (by decide) (by decide) (by decide) (by decide) wordsZ)
  have valueY : MontgomeryAt w (stackPtr s-112#64) selected.negate.y :=
    negY.of_bytes_eq (fun i hi => kept (off := 112) (len := 32) (by decide) (by decide) (by omega) (by omega) hi)
  refine ⟨fuel, w, run, data, effect.rip, valueX, ?_, ?_⟩
  · simpa [BitVec.sub_eq_add_neg, BitVec.add_assoc] using valueY
  · simpa [Projective.negate, BitVec.sub_eq_add_neg, BitVec.add_assoc] using valueZ

end P256.Proofs.Verifying.Combination.Loop.Multi
