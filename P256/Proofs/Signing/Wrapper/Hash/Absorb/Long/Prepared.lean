import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Count
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.SetupFrame
import P256.Proofs.HMAC.Finalize.Copy
import P256.Proofs.Verifying.Message.Hash.Long.Tail.Length

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Prepared [Bindings] (initial start t : RamState)
    (message : ByteArray) : Prop extends Frame initial start t where
  rip : t.RIP = 0x10282b
  source : t.regValue .r15 = start.regValue .rsi + BitVec.ofNat 64 (64 * (message.size / 64))
  length : t.regValue .r12 = BitVec.ofNat 64 (message.size % 64)
  inputPointer : t.regValue .rsi = start.regValue .rsi
  outputPointer : t.regValue .rdi = frameBase initial + 240#64
  countRegister : t.regValue .rdx = BitVec.ofNat 64 (message.size / 64)
  hash : SHA256.HashStateAt t (frameBase initial + 240#64) SHA256.initialHash
  count : loadBytes t.external (frameBase initial + 272#64) 8 = .ok (BitVec.ofNat 64 (message.size / 64))

theorem prepare [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (entered : Entered initial start s message) (large : 64 ≤ message.size) :
    ∃ u, Prepared initial start u message := by
  have rip : s.RIP = 0x1027fd := by simpa only [show ¬ message.size < 64 by omega, ite_false] using entered.rip
  obtain ⟨fuelB, b, runB, readyB, _, effectB⟩ := Count.run (returnBoundary initial)
    (outside pre.context) s (readyToStep entered.machine entered.bindingsSupported)
    (Count.code entered.loaded) rip
  have agreesB : AgreesExcept [.reg 7,.reg 15,.reg 12,.reg 5,.flags,.rip] s b := effectB.agrees
  have frameB := entered.toFrame.after_registers pre.context runB readyB agreesB
    (by simp [Component.Covers]) (by simp)
  have memoryB : b.external = s.external := agreesB.external (by simp [Component.Covers])
  have fields := effectB.writes
  change b.regValue .rdi = stackPtr s + 240 ∧
    b.regValue .r15 = (0x7fffffffffffffc0 &&& s.regValue .rbp) + s.regValue .rsi ∧
    b.regValue .r12 = ((s.regValue .rbp).setWidth 32 &&& 63).setWidth 64 ∧
    b.regValue .rbp = s.regValue .rbp >>> 6 at fields
  have sizeBound := message_size pre
  have countB : b.regValue .rbp = BitVec.ofNat 64 (message.size / 64) := by
    rw [fields.2.2.2, entered.length]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega : message.size < 2^64),
      Nat.mod_eq_of_lt (by omega : message.size / 64 < 2^64)]
  obtain ⟨fuelU, u, runU, readyU, _, effectU⟩ := Setup.run (returnBoundary initial)
    (outside pre.context) b (readyToStep frameB.machine frameB.bindingsSupported)
    (Setup.code frameB.loaded) (Setup.pre pre frameB effectB.rip)
  have frameU := Setup.frame pre frameB runU readyU effectU
  have rspB : stackPtr b = frameBase initial := frameB.rsp
  have rspU : stackPtr u = frameBase initial := frameU.rsp
  have kept {offset len : Nat} (bound : offset + len ≤ 272) :
      ∀ i < len, u.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    have h := Setup.kept effectU bound
    simpa only [rspB, memoryB] using h
  have stores := effectU.writes
  change memLoad u.external (stackPtr b + 272#64) 64 = b.regValue .rbp ∧
    u.regValue .rdx = b.regValue .rbp at stores
  rw [countB] at stores
  have countU : loadBytes u.external (frameBase initial + 272#64) 8 =
      .ok (BitVec.ofNat 64 (message.size / 64)) := by
    have readable := stack_readable pre.context frameU (offset := 272) (len := 8) (by decide)
    have alloc : ∀ i < 8, (u.external[stackPtr b + 272#64 + BitVec.ofNat 64 i]?).isSome := by
      rw [rspB]
      simpa only [rspU, BitVec.ofNat_eq_ofNat] using readable.mem
    have bytes := Bytes.of_memLoad (n := 64) alloc
    change Bytes u.external (stackPtr b + 272#64) 8
      (storedByte (memLoad u.external (stackPtr b + 272#64) 64)) at bytes
    rw [stores.1] at bytes
    simpa only [rspB] using bytes.loadBytes64
  have hashU : SHA256.HashStateAt u (frameBase initial + 240#64) SHA256.initialHash := by
    have hashS : SHA256.HashStateAt s (frameBase initial + 240#64) SHA256.initialHash := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        (show SHA256.HashStateAt s (frameBase initial + 176#64 + 64#64) SHA256.initialHash from entered.hash.hash)
    exact hashS.copy (kept (offset := 240) (len := 32) (by decide))
  have aU : AgreesExcept [.mem (stackPtr b + 272#64) 8,.reg 2,.rip] b u := by
    simpa only [Setup.effect, Effect.components, Write.component, Operand.component,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.ofNat_eq_ofNat] using effectU.agrees
  refine ⟨u, frameU, effectU.rip, ?_, ?_, ?_, ?_, stores.2, hashU, countU⟩
  · apply (aU.read (n := 64) (r := 15) (by simp)).trans
    change b.regValue .r15 = _
    rw [fields.2.1, entered.length, entered.pointer, BitVec.and_comm,
      Verifying.Message.Hash.Long.Tail.full_length_ofNat sizeBound, BitVec.add_comm]
  · apply (aU.read (n := 64) (r := 12) (by simp)).trans
    change b.regValue .r12 = _
    rw [fields.2.2.1, entered.length,
      Verifying.Message.Hash.Long.Tail.tail_length_ofNat sizeBound]
  · exact (aU.read (n := 64) (r := 6) (by simp)).trans
      ((agreesB.read (n := 64) (r := 6) (by simp)).trans entered.pointer)
  · exact (aU.read (n := 64) (r := 7) (by simp)).trans
      (fields.1.trans (congrArg (· + 240) entered.rsp))

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long
