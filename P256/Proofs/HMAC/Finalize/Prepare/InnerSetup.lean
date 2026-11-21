import P256.Proofs.HMAC.Finalize.Prepare.Interface
import P256.Proofs.HMAC.Finalize.InnerSetup
import P256.Proofs.HMAC.Finalize.Frame

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

theorem inner_setup_memory {s t : RamState} (pre : InnerSetup.Pre s)
    (position : s.external[stackPtr s + 239]? = some 0)
    (effect : (InnerSetup.effect s).Holds s t) :
    ∀ a : BitVec 64, t.external[a]? = s.external[a]? := by
  have word : memLoad t.external (stackPtr s + 239) 8 = 0 := effect.writes.1
  have bytes := Bytes.of_memLoad (n := 8) (a := stackPtr s + 239)
    (m := t.external) (pre.writable.of_holds effect).mem
  rw [word] at bytes
  have zero : t.external[stackPtr s + 239]? = some 0 := by
    simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl] using bytes 0 (by decide)
  intro a
  by_cases ha : a = stackPtr s + 239
  · rw [ha, zero, position]
  · apply effect.agrees.byte
    intro c hc covered
    simp only [InnerSetup.effect, Effect.components, Write.component, List.map_cons,
      List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, Operand.component, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    obtain ⟨i, hi, eq⟩ := covered
    have iz : i = 0 := by omega
    exact ha (by simpa [iz, rspOf, stackPtr, Operand.read] using eq)

theorem inner_setup [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key input : ByteArray} (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : OuterReady initial s key input) :
    ∃ fuel t, Advances boundary fuel s t ∧ CopyReady initial t key input := by
  have hp : InnerSetup.Pre s := by
    refine ⟨state.rip, ?_, ?_⟩
    · have hw := ScalarFrame.stack_writable (stackPre pre) state.toFrameState (by decide) (offset := 239) (len := 1)
        (by decide) (by decide)
      exact ⟨hw.low, hw.mem, hw.tables⟩
    · exact ScalarFrame.stack_code (stackPre pre) state.toFrameState (by decide) (offset := 239) (len := 1)
        (by decide) (codeOffset := 0xf9b) (by decide)
  obtain ⟨fuel, t, run, ready, _, effect⟩ :=
    InnerSetup.run boundary pre.outerBoundary s (readyToStep state.machine state.bindingsSupported)
      (InnerSetup.code state.loaded) hp
  have memory := inner_setup_memory hp (by
    simp only [BitVec.ofNat_eq_ofNat]
    rw [stack_address state.rsp (by decide : 239 ≤ 328)]
    have pos := state.outer.position
    simpa only [keyPad_size, Nat.reduceMod, show UInt8.ofNat 0 = (0 : UInt8) from rfl,
      Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using pos) effect
  have frame : ScalarFrame.FrameState initial t 0 672 328 := by
    apply state.toFrameState.after_effect (stackPre pre) (by decide) ready effect.agrees
    · intro c hc a covered
      simp only [InnerSetup.effect, Effect.components, Write.component, List.map_cons,
        List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, Operand.component, or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      exact ⟨workRegion initial 672, by simp,
        local_work_contains pre state.rsp (by decide) covered⟩
    · simp [InnerSetup.effect, Effect.components]
  have writes := effect.writes
  change memLoad t.external (stackPtr s + 239) 8 = 0 ∧
    t.regValue .r15 = s.regValue .r15 + 64 ∧
    t.regValue .rdi = stackPtr s + 72 ∧
    t.regValue .rcx = 13 ∧ t.regValue .rsi = s.regValue .r15 + 64 at writes
  refine ⟨fuel, t, run, frame, effect.rip,
    (effect.agrees.read (n := 64) (r := 3) (by simp [InnerSetup.effect, Effect.components])).trans state.outputPointer,
    ?_, ?_, writes.2.2.2.1,
    state.state.inner.copy (fun i hi => memory _),
    state.outer.copy (fun i hi => memory _)⟩
  · simpa only [state.sourcePointer] using writes.2.2.2.2
  · rw [writes.2.2.1]
    have sp := effect.agrees.read (n := 64) (r := 4) (by simp [InnerSetup.effect, Effect.components])
    change stackPtr t = stackPtr s at sp
    rw [sp]

end P256.Proofs.HMAC.Finalize.Prepare
