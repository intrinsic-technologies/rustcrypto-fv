import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Interface
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.FillSetup
import P256.Proofs.HMAC.State
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem mark [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Loaded initial start s message) :
    ∃ t, Marked initial start t message := by
  have rem : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have address : rspOf s + (Operand.reg 3 : Operand 64).read s + 64 =
      frameBase initial + 64 + BitVec.ofNat 64 (message.size % 64) := by
    change stackPtr s + s.regValue .rbx + 64 = _
    rw [state.position, state.rsp]
    simp only [frameBase, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (message.size % 64))]
  have localAddress : rspOf s + (Operand.reg 3 : Operand 64).read s + 64 =
      stackPtr s + BitVec.ofNat 64 (message.size % 64 + 64) := by
    change stackPtr s + s.regValue .rbx + 64 = _
    simp only [state.position, BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  have setup : FillSetup.Pre s := by
    refine ⟨state.rip, ?_, ?_⟩
    · rw [localAddress]
      have w := stack_writable pre.context state.toFrame
        (offset := message.size % 64 + 64) (len := 1) (by omega) (by decide)
      exact ⟨w.low, w.mem, w.tables⟩
    · rw [localAddress]
      exact stack_code pre.context state.toFrame
        (offset := message.size % 64 + 64) (len := 1) (by omega) (codeOffset := 0x287d) (codeLen := 18) (by decide)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := FillSetup.run (returnBoundary initial) (outside pre.context) s
    (readyToStep state.machine state.bindingsSupported) (FillSetup.code state.loaded) setup
  have writes : WritesWithin (FillSetup.effect s).components
      #v[workRegion initial] := by
    intro c hc a covered
    simp only [FillSetup.effect, Effect.components, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | rfl) | rfl
    all_goals try exact covered.elim
    rw [localAddress, ScalarFrame.scalar_stack_address (frameOffset := 520) state.rsp
      (by decide : 520 < 2^64) (by omega)] at covered
    exact ⟨_, by simp, work_contains pre.context
      (by omega) (by omega) covered⟩
  have frame := state.toFrame.after_effect pre.context run ready effect.agrees writes
    ((effect.agrees.read (n := 64) (r := 4)
      (by simp [FillSetup.effect, Effect.components])).trans state.rsp)
    (by simp [FillSetup.effect, Effect.components])
  have bytes (i : Nat) (hi : i < 280) (ne : i ≠ message.size % 64 + 64) :
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
    simp only [BitVec.add_assoc] at eq
    have eqn := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp eq)
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at eqn
    exact ne (by omega)
  have fields := effect.writes
  change memLoad t.external (rspOf s + (Operand.reg 3 : Operand 64).read s + 64) 8 = 128 ∧
    t.regValue .rdi = rspOf s + (Operand.reg 3 : Operand 64).read s + 65 ∧
    t.regValue .rsi = 0 ∧ t.regValue .rdx = s.regValue .r12 at fields
  refine ⟨t, {
    toLive := ⟨frame⟩
    rip := effect.rip
    hash := ?_
    tail := hasBytes_copy state.tail (fun i hi => by
      simpa only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
        bytes (64+i) (by omega) (by omega))
    marker := ?_
    hashPointer := (effect.agrees.read (n := 64) (r := 15)
      (by simp [FillSetup.effect, Effect.components])).trans state.hashPointer
    count := (effect.agrees.read (n := 64) (r := 14)
      (by simp [FillSetup.effect, Effect.components])).trans state.count
    position := (effect.agrees.read (n := 64) (r := 3)
      (by simp [FillSetup.effect, Effect.components])).trans state.position
    remaining := (effect.agrees.read (n := 64) (r := 12)
      (by simp [FillSetup.effect, Effect.components])).trans state.remaining
    destination := ?_
    zero := fields.2.2.1
    length := fields.2.2.2.trans state.remaining }⟩
  · apply state.hash.copy
    intro i hi
    have byte := bytes (128+i) (by omega) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using byte
  · have marker := fields.1
    rw [address, memLoad_8] at marker
    change ((t.external[frameBase initial + 64 + BitVec.ofNat 64 (message.size % 64)]?).getD 0).toBitVec = 128 at marker
    cases byte : t.external[frameBase initial + 64 + BitVec.ofNat 64 (message.size % 64)]? with
    | none => rw [byte] at marker; contradiction
    | some v =>
      simp only [byte, Option.getD_some] at marker
      exact congrArg some (UInt8.eq_of_toBitVec_eq marker)
  · rw [fields.2.1]
    change stackPtr s + s.regValue .rbx + 65 = _
    rw [state.position]
    rw [state.rsp, BitVec.ofNat_add, BitVec.add_assoc]
    rfl

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad
