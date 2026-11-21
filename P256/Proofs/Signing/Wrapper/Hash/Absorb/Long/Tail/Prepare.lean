import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Compression
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Interface
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Setup
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem prepare [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) (state : Compressed initial start s message) :
    ∃ t, Ready initial start t message := by
  have hp : StorePre 0x102830 8 (fun s => rspOf s + 239) 1 s := by
    refine ⟨state.rip, ?_, ?_⟩
    · have w := stack_writable pre.context state.toFrame
        (offset := 239) (len := 1) (by decide) (by decide)
      exact ⟨w.low, w.mem, w.tables⟩
    · exact stack_code pre.context state.toFrame
        (offset := 239) (len := 1) (codeOffset := 0x2830) (by decide) (by decide)
  obtain ⟨b, runB, readyB, effectB⟩ := Store.run
    (readyToStep state.machine state.bindingsSupported) state.loaded hp (outside pre.context)
  have frameB := store_frame pre.context state.toFrame runB readyB effectB
  have agreesB : AgreesExcept [.mem (stackPtr s + 239) 1,.rip] s b := by
    have h := effectB.agrees
    simp only [Store.effect, Effect.components, Write.component, Operand.component,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append] at h
    exact h
  have prefixSource : b.regValue .r15 = start.regValue .rsi +
      BitVec.ofNat 64 (64 * (message.size / 64)) :=
    (agreesB.read (n := 64) (r := 15) (by simp)).trans state.source
  have prefixLength : b.regValue .r12 = BitVec.ofNat 64 (message.size % 64) :=
    (agreesB.read (n := 64) (r := 12) (by simp)).trans state.length
  obtain ⟨fuelT, t, runT, readyT, _, effectT⟩ := Setup.run (returnBoundary initial)
    (outside pre.context) b readyB (Setup.code frameB.loaded) effectB.rip
  have agreesT : AgreesExcept [.reg 7,.reg 6,.reg 2,.rip] b t := effectT.agrees
  have memoryT := agreesT.external (by simp [Component.Covers])
  have frameT := frameB.after_registers pre.context runT readyT agreesT
    (by simp [Component.Covers]) (by simp)
  have rsp : stackPtr s = frameBase initial := state.rsp
  have kept {offset len : Nat} (bound : offset + len < 2^64)
      (apart : offset + len ≤ 239 ∨ 240 ≤ offset) {i : Nat} (hi : i < len) :
      t.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    rw [memoryT]
    have h := store_byte effectB bound apart hi
    simpa only [rsp] using h
  have fieldsT := effectT.writes
  change t.regValue .rdi = stackPtr b + 176 ∧ t.regValue .rsi = b.regValue .r15 ∧
    t.regValue .rdx = b.regValue .r12 at fieldsT
  refine ⟨t, {
    toFrame := frameT
    rip := effectT.rip
    source := fieldsT.2.1.trans prefixSource
    destination := fieldsT.1.trans (congrArg (· + 176) frameB.rsp)
    length := fieldsT.2.2.trans prefixLength
    hash := state.hash.copy (fun i hi => kept (by decide) (.inr (by decide)) hi)
    count := loadBytes_ok_copy (fun i hi => kept (by decide) (.inr (by decide)) hi) state.count
    position := ?_ }⟩
  rw [memoryT]
  have store := effectB.writes
  change memLoad b.external (stackPtr s + 239) 8 = (s.regValue .r12).setWidth 8 at store
  rw [state.length, BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64)] at store
  have raw := Bytes.of_memLoad (n := 8) (hp.write.readable.of_holds effectB).mem
  change Bytes b.external (stackPtr s + 239) 1
    (storedByte (memLoad b.external (stackPtr s + 239) 8)) at raw
  rw [store] at raw
  have h := raw 0 (by decide)
  have byte : storedByte (BitVec.ofNat 8 (message.size % 64)) 0 = UInt8.ofNat (message.size % 64) := by
    simp only [storedByte, Nat.mul_zero, Nat.shiftRight_zero, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : message.size % 64 < 2^8)]
  simpa only [rsp, BitVec.ofNat_eq_ofNat, BitVec.add_zero, byte] using h

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail
