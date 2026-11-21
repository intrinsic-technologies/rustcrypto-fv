import Sha2.Proofs.Common.Machine.MemoryFrame
import Sha2.Proofs.Wrapper512.Absorb.Large.Call
import Sha2.Proofs.Wrapper512.Absorb.Large.Counter
import Sha2.Proofs.Wrapper512.Absorb.Large.Memory
import Sha2.Proofs.Wrapper512.Absorb.Large.Finish
import Sha2.Proofs.Wrapper512.Absorb.Large.CompressSetup
import Sha2.Proofs.Common.SHA256.Finalize.Proof.Compress.Call

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512

structure Result [Bindings] (v : Variant) (initial s t : RamState) (hash : Array UInt64) (chunk : ByteArray) (form : Form := .slices) : Prop where
  preserved : Preserved v initial t form
  rip : t.RIP = v.pc (finishMoveOffset v form + 3) form
  hashWords : HashStateAt t (stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash)
    (NIST.SHA512.compress hash (NIST.Encoding.octetsToBits chunk))
  blocks : memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 =
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 + 1
  blocksHigh : memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 =
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 +
      (if (addSpec (memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64) 1).2.CF then 1 else 0)
  source : v.sourceValue form t =
    (.reg (if form = .slices then 3 else BitVec.ofNat 5 (v.traversal form).lengthReg) : Operand 64).read s
  restRegister : (.reg (v.restRegister form) : Operand 64).read t =
    (.reg (v.restRegister form) : Operand 64).read s
  indexRegister : v.indexValue form t = v.indexValue form s
  countRegister : v.countValue form initial t = v.countValue form initial s
  bufferRegister : form = .reset 1 → t.regValue .rbx = s.regValue .rbx
  outputSaved : form = .traitFinalizeIntoReset false →
    memLoad t.external (outputSavePointer initial form) 64 = memLoad s.external (outputSavePointer initial form) 64
  memcpyTarget : match form with
    | .reset stage => stage.val = 2 → t.regValue .rbx = s.regValue .rbx
    | .finalizeIntoReset true =>
      t.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) =
        s.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12)
    | .traitFinalizeIntoReset second =>
      t.regValue (if second then .rbp else .r13) = s.regValue (if second then .rbp else .r13)
    | _ => True
  activeBufferRegister : ∀ second, form = .traitFinalizeIntoReset second →
    t.regValue .rbx = bufferPointer initial form form.activeMemory
  tailLength : t.external[stackPtr initial - BitVec.ofNat 64 form.activeMemory.tail]? = some 0
  execution : ∃ fuel, Advances (returnBoundary initial) fuel s t
  stackFrame : MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes]


theorem compressRegisterFacts (v : Variant) (form : Form) :
    finishSourceRegister v form ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
    Component.reg (finishSourceRegister v form) ∉ CompressSetup.formComponents form ∧
    ∀ r ∈ [v.restRegister form, BitVec.ofNat 5 (v.traversal form).indexReg],
      r ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
      Component.reg r ∉ CompressSetup.formComponents form ∧ r ≠ finishTargetRegister v form := by
  cases form <;> cases v <;> decide +revert +kernel

theorem compressCountFacts (v : Variant) (form : Form) :
    match (v.traversal form).countReg with
    | some n =>
      BitVec.ofNat 5 n ∈ ([3,5,12,13,14,15] : List (BitVec 5)) ∧
      Component.reg (BitVec.ofNat 5 n) ∉ CompressSetup.formComponents form ∧
      BitVec.ofNat 5 n ≠ finishTargetRegister v form
    | none => (v.traversal form).countSlot = some 640 ∧
      (form = .traitFinalizeIntoReset false ∨ form = .traitFinalizeIntoReset true) := by
  have countCases : (v.traversal form).countReg = some 12 ∨
      (v.traversal form).countReg = some 15 ∨ (v.traversal form).countReg = none := by
    cases form <;> cases v <;> decide +revert +kernel
  rcases countCases with h | h | h
  all_goals rw [h]
  all_goals revert h
  all_goals cases form <;> cases v <;> decide +revert +kernel

theorem compressSetupLength (form : Form) : (CompressSetup.formBytes form).length ≤ 21 := by
  cases form <;> decide +revert +kernel

theorem compress [Bindings] (body : Compression.BlockCorrect) {v : Variant} {form : Form}
    {initial s : RamState} {inputs : Array Input} {hash : Array UInt64} {chunk : ByteArray}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form)
    (rip : s.RIP = v.pc (Counter.addOffset false v form) form)
    (words : HashStateAt s (stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash) hash)
    (bytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer).toNat, 128⟩ : MemoryRegion).HasBytes s.external chunk)
    (nonDigest : form ≠ .digest := by decide)
    (bufferRegister : form = .reset 1 → s.regValue .rbx = bufferPointer initial form := by simp)
    (outputSaved : form = .traitFinalizeIntoReset false →
      memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx := by simp) :
    ∃ t, Result v initial s t hash chunk form := by
  obtain ⟨u, preservedU, ripU, blocksU, highU, frameU, ⟨fuelU, runU⟩, stackU⟩ := Counter.increment ctx input rip nonDigest
  have wordsU : HashStateAt u (stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash) hash :=
    hashState_of_bytes words (counter_bytes frameU (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) (by decide))
  have bytesU : (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer).toNat,128⟩ : MemoryRegion).HasBytes u.external chunk := by
    refine ⟨bytes.1, fun i => ?_⟩
    have hi : i.val < 128 := by have hsize : chunk.size = 128 := bytes.1; omega
    have byte := bytes.2 i
    change u.external[BitVec.ofNat 64 ((stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer).toNat+i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [counter_bytes frameU (offset := BitVec.ofNat 64 form.activeMemory.buffer) (len := 128)
      (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) (by decide) i.val hi]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using byte
  obtain ⟨fuelV, w, runV, readyV, _, effectV⟩ := CompressSetup.run_form v form nonDigest
    (returnBoundary initial) (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 u
    (supportedMachine_readyToStep preservedU.machine)
    (programText_slice (programLoaded_codeIn preservedU.loaded)
      (v.textOffset form + Counter.endOffset false v form) _
      (by have h := CompressSetup.form_bound v form
          have length := compressSetupLength form
          omega)
      (CompressSetup.form_bytes v form nonDigest)) ripU
  obtain ⟨ripV, destinationV, sourceV, countV, frameV⟩ := CompressSetup.form_result v form nonDigest
    effectV preservedU.rsp (fun hf => (frameU.read (n := 64) (r := 3) (by simp)).trans (bufferRegister hf))
  change AgreesExcept (CompressSetup.formComponents form) u w at frameV
  have preservedV := preserved_of_agrees ctx preservedU runV readyV frameV
    (by cases form <;> simp [CompressSetup.formComponents, LocalWrites, Component.Covers])
    (by cases form <;> simp [CompressSetup.formComponents]) (by cases form <;> simp [CompressSetup.formComponents])
    (by intro h; exact (nonDigest h).elim)
    (by intro h; subst form; left; cases v <;> simp [CompressSetup.formComponents])
  have memoryV : w.external = u.external := frameV.external (by cases form <;> simp [CompressSetup.formComponents, Component.Covers])
  have wordsV := hashState_of_bytes wordsU (fun i _ => by rw [memoryV])
  have bytesV : (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.buffer).toNat,128⟩ : MemoryRegion).HasBytes w.external chunk := by
    rw [memoryV]; exact bytesU
  obtain ⟨x, preservedW, ripW, wordsW, blocksW, highW, abiW, memoryW, ⟨fuelW, runW⟩, stackW⟩ :=
    compression_call body ctx preservedV wordsV ripV destinationV sourceV countV bytesV nonDigest
  have memoryWG : MemoryWriteFrame w x #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 form.activeMemory.hash).toNat,64⟩ : MemoryRegion),
      (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes+424)).toNat,(form.frameBytes+424)-form.frameBytes⟩ : MemoryRegion)] := by
    simpa only [Nat.add_sub_cancel_left] using memoryW
  have beforeBytes (offset len : Nat) (low : offset ≤ form.frameBytes) (high : len ≤ offset)
      (counterLow : OffsetsApart (-BitVec.ofNat 64 form.activeMemory.countLow) 8 (-BitVec.ofNat 64 offset) len)
      (counterHigh : OffsetsApart (-BitVec.ofNat 64 form.activeMemory.countHigh) 8 (-BitVec.ofNat 64 offset) len)
      (hashApart : form.activeMemory.hash + len ≤ offset ∨ offset + 64 ≤ form.activeMemory.hash)
      (small : 8+len < 2^64) :
      ∀ i < len, x.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    rw [frame_bytes ctx memoryWG (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) low high hashApart i hi,
      memoryV]
    exact counter_bytes frameU counterLow counterHigh small i hi
  have outputW : form = .traitFinalizeIntoReset false →
      memLoad x.external (outputSavePointer initial form) 64 = initial.regValue .rcx := by
    intro hf
    rw [← outputSaved hf]
    apply memLoad_congr; intro i hi
    exact congrArg (fun value : Option UInt8 => value.getD 0)
      (beforeBytes form.outputSlot 8 (by subst form; decide) (by subst form; decide)
        (by subst form; unfold OffsetsApart; decide +kernel) (by subst form; unfold OffsetsApart; decide +kernel)
        (by subst form; decide) (by decide) i hi)
  obtain ⟨t, preservedT, ripT, sourceT, tailT, frameT, ⟨fuelT, runT⟩, stackT⟩ := finish ctx preservedW ripW nonDigest outputW
  have afterBytes (offset len : Nat)
      (apart : OffsetsApart (-BitVec.ofNat 64 form.activeMemory.tail) 1 (-BitVec.ofNat 64 offset) len)
      (small : 1+len < 2^64) :=
    bytes_of_mem_frame frameT (by simp [Component.Covers]) apart small
  have wordsT := hashState_of_bytes wordsW (afterBytes form.activeMemory.hash 64 (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) (by decide))
  have blocksT : memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 =
      memLoad x.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countLow) 64 := by
    apply memLoad_congr; intro i hi
    exact congrArg (fun value : Option UInt8 => value.getD 0)
      (afterBytes form.activeMemory.countLow 8 (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) (by decide) i hi)
  have highT : memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 =
      memLoad x.external (stackPtr initial - BitVec.ofNat 64 form.activeMemory.countHigh) 64 := by
    apply memLoad_congr; intro i hi
    exact congrArg (fun value : Option UInt8 => value.getD 0)
      (afterBytes form.activeMemory.countHigh 8 (by cases form <;> dsimp only [Form.activeMemory, Form.bufferedMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory, ResetLayout.cloneMemory, ResetLayout.finalizeMemory, CompressSetup.formBytes, CompressSetup.bytes, CompressSetup.registerBufferBytes, CompressSetup.buffer8Bytes, CompressSetup.savedBufferBytes, OffsetsApart] <;> decide +kernel) (by decide) i hi)
  have readBefore (r : BitVec 5) (kept : Component.reg r ∉ CompressSetup.formComponents form) :
      (.reg r : Operand 64).read w = (.reg r : Operand 64).read s :=
    (frameV.read kept).trans (frameU.read (by simp))
  have readAfter (r : BitVec 5) (saved : r ∈ ([3,5,12,13,14,15] : List (BitVec 5)))
      (setup : Component.reg r ∉ CompressSetup.formComponents form) (different : r ≠ finishTargetRegister v form) :
      (.reg r : Operand 64).read t = (.reg r : Operand 64).read s :=
    (frameT.read (by simp [different])).trans
      ((Common.SHA256.Finalize.Compress.abi_read abiW saved).trans (readBefore r setup))
  have allBytes (offset len : Nat) (low : offset ≤ form.frameBytes) (high : len ≤ offset)
      (counterLow : OffsetsApart (-BitVec.ofNat 64 form.activeMemory.countLow) 8 (-BitVec.ofNat 64 offset) len)
      (counterHigh : OffsetsApart (-BitVec.ofNat 64 form.activeMemory.countHigh) 8 (-BitVec.ofNat 64 offset) len)
      (hashApart : form.activeMemory.hash + len ≤ offset ∨ offset + 64 ≤ form.activeMemory.hash)
      (tailApart : OffsetsApart (-BitVec.ofNat 64 form.activeMemory.tail) 1 (-BitVec.ofNat 64 offset) len)
      (small : 8+len < 2^64) :
      ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    intro i hi
    exact (afterBytes offset len tailApart (by omega) i hi).trans
      (beforeBytes offset len low high counterLow counterHigh hashApart small i hi)
  refine ⟨t, preservedT, ripT, wordsT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, tailT, ⟨_, ((runU.trans runV).trans runW).trans runT⟩,
    memoryWriteFrame_trans stackU (memoryWriteFrame_trans
      (frameV.memoryWriteFrame (by cases form <;> simp [CompressSetup.formComponents, WritesWithin, Component.Covers]))
      (memoryWriteFrame_trans stackW stackT))⟩
  · rw [blocksT, blocksW, memoryV]; exact blocksU
  · rw [highT, highW, memoryV]
    have carry (b : Bool) : BitVec.ofNat 64 b.toNat = if b then 1 else 0 := by cases b <;> rfl
    simpa only [carry] using highU
  · exact sourceT.trans ((Common.SHA256.Finalize.Compress.abi_read abiW (compressRegisterFacts v form).1).trans
      (readBefore _ (compressRegisterFacts v form).2.1))
  · obtain ⟨a,b,c⟩ := (compressRegisterFacts v form).2.2 (v.restRegister form) (by simp)
    exact readAfter _ a b c
  · obtain ⟨a,b,c⟩ := (compressRegisterFacts v form).2.2 (BitVec.ofNat 5 (v.traversal form).indexReg) (by simp)
    exact readAfter _ a b c
  · have facts := compressCountFacts v form
    cases hreg : (v.traversal form).countReg with
    | some n =>
      simp only [hreg] at facts
      simpa only [Variant.countValue, hreg] using readAfter _ facts.1 facts.2.1 facts.2.2
    | none =>
      simp only [hreg] at facts
      simp only [Variant.countValue, hreg]
      obtain ⟨slot, hf⟩ := facts
      rw [slot]
      rcases hf with rfl | rfl
      all_goals
        apply memLoad_congr
        intro i hi
        exact congrArg (fun value : Option UInt8 => value.getD 0)
          (allBytes 640 8 (by decide) (by decide) (by unfold OffsetsApart; decide +kernel)
            (by unfold OffsetsApart; decide +kernel) (by decide) (by unfold OffsetsApart; decide +kernel) (by decide) i hi)
  · intro hf
    have facts : (3 : BitVec 5) ≠ finishTargetRegister v form ∧ Component.reg 3 ∉ CompressSetup.formComponents form := by
      subst form
      cases v <;> decide +kernel
    exact readAfter 3 (by simp) facts.2 facts.1
  · intro hf
    subst form
    apply memLoad_congr; intro i hi
    exact congrArg (fun value : Option UInt8 => value.getD 0)
      (allBytes (Form.traitFinalizeIntoReset false).outputSlot 8 (by decide) (by decide)
        (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)
        (by decide) (by unfold OffsetsApart; decide +kernel) (by decide) i hi)
  · cases form with
    | slices | digest => trivial
    | reset stage =>
      intro hv
      have hs : stage = (2 : Fin 3) := Fin.ext hv
      subst stage
      cases v <;> exact readAfter 3 (by decide) (by decide) (by decide)
    | finalizeIntoReset second =>
      cases second
      · trivial
      · cases v <;> first
          | exact readAfter 3 (by decide) (by decide) (by decide)
          | exact readAfter 12 (by decide) (by decide) (by decide)
    | traitFinalizeIntoReset second =>
      cases second <;> cases v <;> first
        | exact readAfter 13 (by decide) (by decide) (by decide)
        | exact readAfter 5 (by decide) (by decide) (by decide)
  · intro second hf
    subst form
    have bufferV : w.regValue .rbx = bufferPointer initial (.traitFinalizeIntoReset second)
        (Form.traitFinalizeIntoReset second).activeMemory := by
      have writes := effectV.writes
      change w.regValue .rdx = 1 ∧ w.regValue .rdi = _ ∧
        w.regValue .rbx = _ ∧ w.regValue .rsi = _ at writes
      exact writes.2.2.1.trans (writes.2.2.2.symm.trans sourceV)
    exact (frameT.read (n := 64) (r := 3) (by
      have different : (3 : BitVec 5) ≠ finishTargetRegister v (.traitFinalizeIntoReset second) := by
        cases v <;> cases second <;> decide +kernel
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq]
      intro member
      rcases member with impossible | same
      · exact impossible
      · injection same with eq
        exact different eq)).trans ((abiW.1 .rbx (by simp)).trans bufferV)

end Sha2.Proofs.Wrapper512.Absorb.Large
