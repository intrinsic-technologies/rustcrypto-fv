import P256.Proofs.Verifying.Message.Hash.Long.Compression
import P256.Proofs.Verifying.Message.Hash.Long.Tail.Interface
import P256.Proofs.Verifying.Message.Hash.Long.Tail.Prefix
import P256.Proofs.Verifying.Message.Hash.Long.Tail.Length
import P256.Proofs.Verifying.Message.Hash.Long.Tail.Setup
import P256.Proofs.Verifying.Message.Hash.Long.Tail.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Tail

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (state : Compressed initial s boundary message) :
    ∃ t, Ready initial t boundary message := by
  have small : message.size < 2^32 := by have h := pre.messageBounded; exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h
  obtain ⟨fuelA, a, runA, readyA, _, effectA⟩ := Prefix.run boundary pre.outerBoundary s
    (readyToStep state.machine state.bindingsSupported) (Prefix.code state.loaded) state.rip
  have agreesA : AgreesExcept [.reg 0,.reg 1,.reg 5,.reg 14,.flags,.rip] s a := effectA.agrees
  have frameA := state.toFrameState.after_registers readyA agreesA (by simp [Component.Covers]) (by simp)
  have memoryA := agreesA.external (by simp [Component.Covers])
  have full : Prefix.fullLength s = BitVec.ofNat 64 (64 * (message.size / 64)) := by
    change s.regValue .rbp &&& _ = _
    rw [state.length]
    exact full_length_ofNat small
  have rem : Prefix.tailLength s = BitVec.ofNat 64 (message.size % 64) := by
    change ((s.regValue .rbp).setWidth 32 &&& 63).setWidth 64 = _
    rw [state.length]
    exact tail_length_ofNat small
  have fieldsA := effectA.writes
  change a.regValue .rax = _ ∧ a.regValue .rcx = _ ∧ a.regValue .rbp = _ ∧
    a.regValue .r14 = s.regValue .r14 + Prefix.fullLength s at fieldsA
  have hp : StorePre 0x10d6e4 8 (fun s => rspOf s + 535) 1 a := by
    refine ⟨effectA.rip, ?_, ?_⟩
    · have w := ScalarFrame.stack_writable pre.toCalleePre frameA
        (offset := 535) (len := 1) (by decide) (by decide) (by decide)
      exact ⟨w.low, w.mem, w.tables⟩
    · exact ScalarFrame.stack_code pre.toCalleePre frameA
        (offset := 535) (len := 1) (codeOffset := 0xd6e4) (by decide) (by decide) (by decide)
  obtain ⟨b, runB, readyB, effectB⟩ := Store.run readyA frameA.loaded hp pre.outerBoundary
  have frameB := store_frame pre.toCalleePre frameA readyB effectB
  have memoryB := work_frame_stack pre.toCalleePre
    (effectB.agrees.memoryWriteFrame (store_writes pre.toCalleePre frameA))
  have agreesB : AgreesExcept [.mem (stackPtr a + 535) 1,.rip] a b := by
    have h := effectB.agrees
    simp only [Store.effect, Effect.components, Write.component, Operand.component,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append] at h
    exact h
  have prefixSource : b.regValue .r14 = memLoad initial.external (initial.regValue .rdx) 64 +
      BitVec.ofNat 64 (64 * (message.size / 64)) := by
    have h : b.regValue .r14 = a.regValue .r14 := agreesB.read (n := 64) (r := 14) (by simp)
    rw [h, fieldsA.2.2.2, state.source, full]
  have prefixLength : b.regValue .rbp = BitVec.ofNat 64 (message.size % 64) :=
    (agreesB.read (n := 64) (r := 5) (by simp)).trans (fieldsA.2.2.1.trans rem)
  obtain ⟨fuelT, t, runT, readyT, _, effectT⟩ := Setup.run boundary pre.outerBoundary b
    readyB (Setup.code frameB.loaded) effectB.rip
  have agreesT : AgreesExcept [.reg 7,.reg 6,.reg 2,.rip] b t := effectT.agrees
  have memoryT := agreesT.external (by simp [Component.Covers])
  have frameT := frameB.after_registers readyT agreesT (by simp [Component.Covers]) (by simp)
  have kept {offset len : Nat} (bound : offset + len < 2^64)
      (apart : offset + len ≤ 535 ∨ 536 ≤ offset) {i : Nat} (hi : i < len) :
      t.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    rw [memoryT]
    have h := store_byte effectB bound apart hi
    simp only [frameA.rsp, memoryA] at h
    exact h
  have savedWord {offset : Nat} (bound : offset + 8 ≤ 535) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun o : Option UInt8 => o.getD 0) (kept (by omega) (.inl bound) hi)
  have current : t.regValue .r13 = initial.regValue .rdx :=
    (agreesT.read (n := 64) (r := 13) (by simp)).trans
      ((agreesB.read (n := 64) (r := 13) (by simp)).trans
        ((agreesA.read (n := 64) (r := 13) (by simp)).trans state.current))
  have endPointer : t.regValue .r12 = initial.regValue .rdx + 16 :=
    (agreesT.read (n := 64) (r := 12) (by simp)).trans
      ((agreesB.read (n := 64) (r := 12) (by simp)).trans
        ((agreesA.read (n := 64) (r := 12) (by simp)).trans state.endPointer))
  have fieldsT := effectT.writes
  change t.regValue .rdi = stackPtr b + 472 ∧ t.regValue .rsi = b.regValue .r14 ∧
    t.regValue .rdx = b.regValue .rbp at fieldsT
  refine ⟨t, {
    toLive := {
      toFrameState := frameT
      execution := ?_
      savedKey := (savedWord (by decide)).trans state.savedKey
      savedOutput := (savedWord (by decide)).trans state.savedOutput
      savedSignature := (savedWord (by decide)).trans state.savedSignature
      stackFrame := ?_ }
    rip := effectT.rip
    current := current
    endPointer := endPointer
    source := fieldsT.2.1.trans prefixSource
    destination := fieldsT.1.trans (congrArg (· + 472) frameB.rsp)
    length := fieldsT.2.2.trans prefixLength
    hash := state.hash.copy (fun i hi => kept (by decide) (.inr (by decide)) hi)
    count := loadBytes_ok_copy (fun i hi => kept (by decide) (.inr (by decide)) hi) state.count
    position := ?_ }⟩
  · obtain ⟨before, beforeRun⟩ := state.execution
    exact ⟨before + fuelA + 1 + fuelT, ((beforeRun.trans runA).trans runB).trans runT⟩
  · intro address outside
    rw [memoryT, memoryB address outside, memoryA]
    exact state.stackFrame address outside
  · rw [memoryT]
    have store := effectB.writes
    change memLoad b.external (stackPtr a + 535) 8 = (a.regValue .rbp).setWidth 8 at store
    rw [fieldsA.2.2.1, rem] at store
    have narrow : (BitVec.ofNat 64 (message.size % 64)).setWidth 8 =
        BitVec.ofNat 8 (message.size % 64) := by bv_omega
    change memLoad b.external (stackPtr a + 535) 8 = (BitVec.ofNat 64 (message.size % 64)).setWidth 8 at store
    rw [narrow] at store
    have raw := Bytes.of_memLoad (n := 8) (hp.write.readable.of_holds effectB).mem
    change Bytes b.external (stackPtr a + 535) 1
      (storedByte (memLoad b.external (stackPtr a + 535) 8)) at raw
    rw [store] at raw
    have h := raw 0 (by decide)
    have byte : storedByte (BitVec.ofNat 8 (message.size % 64)) 0 = UInt8.ofNat (message.size % 64) := by
      simp only [storedByte, Nat.mul_zero, Nat.shiftRight_zero, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : message.size % 64 < 2^8)]
    simp only [frameA.rsp, BitVec.ofNat_eq_ofNat, BitVec.add_zero, byte] at h
    exact h

end P256.Proofs.Verifying.Message.Hash.Long.Tail
