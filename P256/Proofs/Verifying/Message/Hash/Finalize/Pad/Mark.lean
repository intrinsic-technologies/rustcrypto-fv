import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.Interface
import P256.Proofs.Verifying.Message.Hash.Finalize.Pad.FillSetup
import P256.Proofs.HMAC.State
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Pad

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem mark [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Loaded initial s boundary message) :
    ∃ t, Marked initial t boundary message := by
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have address : rspOf s + (Operand.reg 15 : Operand 64).read s + 128 =
      frameBase initial + BitVec.ofNat 64 (128 + message.size % 64) := by
    change stackPtr s + s.regValue .r15 + 128 = _
    rw [state.position, state.rsp]
    simp only [frameBase, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
    rw [BitVec.add_comm (BitVec.ofNat 64 (message.size % 64)) 128#64]
  have localAddress : rspOf s + (Operand.reg 15 : Operand 64).read s + 128 =
      stackPtr s + BitVec.ofNat 64 (128 + message.size % 64) := by
    change stackPtr s + s.regValue .r15 + 128 = _
    rw [state.position]
    bv_omega
  have setup : FillSetup.Pre s := by
    refine ⟨state.rip, ?_, ?_⟩
    · rw [localAddress]
      have w := ScalarFrame.stack_writable (frameOffset := 1176) pre.toCalleePre state.toFrameState (by decide)
        (offset := 128 + message.size % 64) (len := 1) (by omega) (by decide)
      exact ⟨w.low, w.mem, w.tables⟩
    · rw [localAddress]
      exact ScalarFrame.stack_code (frameOffset := 1176) pre.toCalleePre state.toFrameState (by decide)
        (by omega) (codeOffset := 0xd755) (by decide)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := FillSetup.run boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported) (FillSetup.code state.loaded) setup
  have writes : WritesWithin (FillSetup.effect s).components
      #v[ScalarFrame.workRegion initial 9992] := by
    intro c hc a covered
    simp only [FillSetup.effect, Effect.components, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | rfl) | rfl
    all_goals try exact covered.elim
    rw [localAddress, ScalarFrame.scalar_stack_address (frameOffset := 1176) state.rsp
      (by decide : 1176 < 2^64) (by omega)] at covered
    exact ⟨_, by simp, ScalarFrame.work_contains pre.toCalleePre
      (by omega) (by omega) covered⟩
  have frame := state.toFrameState.after_effect pre.toCalleePre (by decide) ready
    effect.agrees (fun c hc a ha => by
      obtain ⟨region, member, inside⟩ := writes c hc a ha
      exact ⟨region, by simpa using Or.inr member, inside⟩)
    (by simp [FillSetup.effect, Effect.components])
    (by simp [FillSetup.effect, Effect.components])
    (by simp [FillSetup.effect, Effect.components])
    (by simp [FillSetup.effect, Effect.components])
  have bytes (i : Nat) (hi : i < 1176) (ne : i ≠ 128 + message.size % 64) :
      t.external[frameBase initial + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 i]? := by
    apply effect.agrees.byte
    intro c hc covered
    simp only [FillSetup.effect, Effect.components, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | rfl) | rfl
    all_goals try exact covered.elim
    obtain ⟨j, hj, eq⟩ := covered
    have jz : j = 0 := by omega
    subst j
    rw [address, BitVec.add_zero] at eq
    have eqn := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp eq)
    simp only [BitVec.toNat_ofNat] at eqn
    exact ne (by omega)
  have saved (offset : Nat) (lo : 192 ≤ offset) (hi : offset + 8 ≤ 1176) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi'
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, bytes (offset + i) (by omega) (by omega)]
  have fields := effect.writes
  change memLoad t.external (rspOf s + (Operand.reg 15 : Operand 64).read s + 128) 8 = 128 ∧
    t.regValue .rdi = rspOf s + (Operand.reg 15 : Operand 64).read s + 129 ∧
    t.regValue .rsi = 0 ∧ t.regValue .rdx = s.regValue .r14 at fields
  refine ⟨t, {
    toLive := {
      toFrameState := frame
      execution := ?_
      savedKey := (saved 456 (by decide) (by decide)).trans state.savedKey
      savedOutput := (saved 384 (by decide) (by decide)).trans state.savedOutput
      savedSignature := (saved 464 (by decide) (by decide)).trans state.savedSignature
      stackFrame := memoryWriteFrame_trans state.stackFrame
        (work_frame_stack pre.toCalleePre (effect.agrees.memoryWriteFrame writes)) }
    rip := effect.rip
    hash := ?_
    tail := hasBytes_copy state.tail (fun i hi => by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using bytes (128+i) (by omega) (by omega))
    marker := ?_
    hashPointer := (effect.agrees.read (n := 64) (r := 3)
      (by simp [FillSetup.effect, Effect.components])).trans state.hashPointer
    count := (effect.agrees.read (n := 64) (r := 12)
      (by simp [FillSetup.effect, Effect.components])).trans state.count
    position := (effect.agrees.read (n := 64) (r := 15)
      (by simp [FillSetup.effect, Effect.components])).trans state.position
    remaining := (effect.agrees.read (n := 64) (r := 14)
      (by simp [FillSetup.effect, Effect.components])).trans state.remaining
    destination := ?_
    zero := fields.2.2.1
    length := fields.2.2.2.trans state.remaining }⟩
  · obtain ⟨before, beforeRun⟩ := state.execution
    exact ⟨before + fuel, beforeRun.trans run⟩
  · apply state.hash.copy
    intro i hi
    have byte := bytes (192+i) (by omega) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using byte
  · have marker := fields.1
    rw [address, memLoad_8] at marker
    change ((t.external[frameBase initial + BitVec.ofNat 64 (128 + message.size % 64)]?).getD 0).toBitVec = 128 at marker
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
    cases byte : t.external[frameBase initial + BitVec.ofNat 64 (128 + message.size % 64)]? with
    | none => rw [byte] at marker; contradiction
    | some v =>
      simp only [byte, Option.getD_some] at marker
      exact congrArg some (UInt8.eq_of_toBitVec_eq marker)
  · have dest : t.regValue .rdi = (rspOf s + (Operand.reg 15 : Operand 64).read s + 128) + 1 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using fields.2.1
    rw [dest, address]
    simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]

end P256.Proofs.Verifying.Message.Hash.Finalize.Pad
