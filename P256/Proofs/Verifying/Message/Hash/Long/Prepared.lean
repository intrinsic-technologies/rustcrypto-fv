import P256.Proofs.Verifying.Message.Hash.Long.Dispatch
import P256.Proofs.Verifying.Message.Hash.Long.Count
import P256.Proofs.Verifying.Message.Hash.Long.SetupFrame
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Prepared [Bindings] (initial t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Frame initial t where
  execution : ∃ fuel, Advances boundary fuel initial t
  rip : t.RIP = 0x10d6c9
  current : t.regValue .r13 = initial.regValue .rdx
  endPointer : t.regValue .r12 = initial.regValue .rdx + 16
  source : t.regValue .r14 = memLoad initial.external (initial.regValue .rdx) 64
  length : t.regValue .rbp = BitVec.ofNat 64 message.size
  inputPointer : t.regValue .rsi = memLoad initial.external (initial.regValue .rdx) 64
  outputPointer : t.regValue .rdi = frameBase initial + 536#64
  countRegister : t.regValue .rdx = BitVec.ofNat 64 (message.size / 64)
  hash : SHA256.HashStateAt t (frameBase initial + 536#64) SHA256.initialHash
  count : loadBytes t.external (frameBase initial + 568#64) 8 = .ok (BitVec.ofNat 64 (message.size / 64))
  savedKey : memLoad t.external (frameBase initial + 456#64) 64 = initial.regValue .rsi
  savedOutput : memLoad t.external (frameBase initial + 384#64) 64 = initial.regValue .rdi
  savedSignature : memLoad t.external (frameBase initial + 464#64) 64 = initial.regValue .r8
  stackFrame : MemoryWriteFrame initial t #v[Stack.region initial 9992]

theorem prepare [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (initialized : Initialized initial s boundary)
    (entered : Entered initial s t boundary message) (large : 64 ≤ message.size) :
    ∃ u, Prepared initial u boundary message := by
  obtain ⟨a, runA, frameA, ripA, agreesA⟩ := dispatch pre entered large
  have lengthA : a.regValue .r15 = BitVec.ofNat 64 message.size :=
    (agreesA.read (n := 64) (r := 15) (by simp)).trans entered.length
  obtain ⟨fuelB, b, runB, frameB, ripB, lengthB, countB, agreesB⟩ :=
    Count.nonzero pre frameA ripA lengthA large
  have memoryB : b.external = s.external :=
    ((agreesA.trans agreesB).external (by simp [Component.Covers])).trans entered.memory
  have sourceB : b.regValue .r14 = memLoad initial.external (initial.regValue .rdx) 64 :=
    ((agreesA.trans agreesB).read (n := 64) (r := 14) (by simp)).trans entered.source
  obtain ⟨fuelU, u, runU, readyU, _, effectU⟩ := Setup.run boundary pre.outerBoundary b
    (readyToStep frameB.machine frameB.bindingsSupported) (Setup.code frameB.loaded)
    (Setup.pre pre frameB ripB)
  have frameU := Setup.frame pre frameB readyU effectU
  have rspB : stackPtr b = frameBase initial := frameB.rsp
  have rspU : stackPtr u = frameBase initial := frameU.rsp
  have kept {offset len : Nat} (bound : offset + len ≤ 568) :
      ∀ i < len, u.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[frameBase initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    have h := Setup.kept effectU bound
    simpa only [rspB, memoryB] using h
  have keptLoad {offset : Nat} (bound : offset + 8 ≤ 568) :
      memLoad u.external (frameBase initial + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (kept bound i hi)
  have initialCount : memLoad b.external (stackPtr b + 568#64) 64 = 0#64 := by
    rw [memoryB, rspB]
    have h := initialized.hash.count
    change loadBytes s.external (frameBase initial + 472#64 + 96#64) 8 = .ok (0#64) at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact (Common.Memory.bytes_of_loadBytes64 (Common.Memory.allocated_of_loadBytes h) h).memLoad
      (by decide) (by decide)
  have stores := effectU.writes
  change memLoad u.external (stackPtr b + 568#64) 64 =
      memLoad b.external (stackPtr b + 568#64) 64 + b.regValue .rdx ∧
    u.regValue .rdi = stackPtr b + 536#64 ∧ u.regValue .rsi = b.regValue .r14 at stores
  rw [initialCount, countB, BitVec.zero_add] at stores
  have countU : loadBytes u.external (frameBase initial + 568#64) 8 =
      .ok (BitVec.ofNat 64 (message.size / 64)) := by
    have readable := ScalarFrame.stack_readable pre.toCalleePre frameU
      (offset := 568) (len := 8) (by decide) (by decide)
    have alloc : ∀ i < 8, (u.external[stackPtr b + 568#64 + BitVec.ofNat 64 i]?).isSome := by
      rw [rspB]
      simpa only [rspU, BitVec.ofNat_eq_ofNat] using readable.mem
    have bytes := Bytes.of_memLoad (n := 64) alloc
    change Bytes u.external (stackPtr b + 568#64) 8
      (storedByte (memLoad u.external (stackPtr b + 568#64) 64)) at bytes
    rw [stores.1] at bytes
    simpa only [rspB] using bytes.loadBytes64
  have hashU : SHA256.HashStateAt u (frameBase initial + 536#64) SHA256.initialHash := by
    have hashS : SHA256.HashStateAt s (frameBase initial + 536#64) SHA256.initialHash := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using (show SHA256.HashStateAt s (frameBase initial + 472#64 + 64#64) SHA256.initialHash from initialized.hash.hash)
    exact hashS.copy (kept (offset := 536) (len := 32) (by decide))
  have saved := initialized_saved initialized
  have aU : AgreesExcept [.mem (stackPtr b + 568#64) 8,.reg 7,.reg 6,.flags,.rip] b u := by
    simpa only [Setup.effect, Effect.components, Write.component, Operand.component,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.ofNat_eq_ofNat] using effectU.agrees
  refine ⟨u, frameU, ?_, effectU.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hashU,
    countU, ?_, ?_, ?_, ?_⟩
  · obtain ⟨fuelT, runT⟩ := entered.execution
    exact ⟨fuelT+3+fuelB+fuelU, ((runT.trans runA).trans runB).trans runU⟩
  · exact (aU.read (n := 64) (r := 13) (by simp)).trans
      (((agreesA.trans agreesB).read (n := 64) (r := 13) (by simp)).trans entered.current)
  · exact (aU.read (n := 64) (r := 12) (by simp)).trans
      (((agreesA.trans agreesB).read (n := 64) (r := 12) (by simp)).trans entered.endPointer)
  · exact (aU.read (n := 64) (r := 14) (by simp)).trans sourceB
  · exact (aU.read (n := 64) (r := 5) (by simp)).trans lengthB
  · exact stores.2.2.trans sourceB
  · simpa only [rspB] using stores.2.1
  · exact (aU.read (n := 64) (r := 2) (by simp)).trans countB
  · exact (keptLoad (offset := 456) (by decide)).trans saved.1
  · exact (keptLoad (offset := 384) (by decide)).trans saved.2.1
  · exact (keptLoad (offset := 464) (by decide)).trans saved.2.2
  · have stackB : MemoryWriteFrame initial b #v[Stack.region initial 9992] := by
      intro address outside
      rw [memoryB]
      exact initialized.stackFrame address outside
    exact memoryWriteFrame_trans stackB
      (work_frame_stack pre.toCalleePre (effectU.agrees.memoryWriteFrame (Setup.writes pre frameB)))

end P256.Proofs.Verifying.Message.Hash.Long
