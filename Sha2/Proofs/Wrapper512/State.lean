import Sha2.Proofs.Program
import Sha2.Proofs.Common.Machine.ExecutionState
import Sha2.Proofs.Wrapper.Inputs
import Sha2.Proofs.Common.Machine.CallReturn
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.Machine.StackRegion
import Sha2.Proofs.Common.SHA512.Interfaces
import Sha2.Proofs.Wrapper512.ResetLayout
import Sha2.Proofs.FIPS180.Computation512

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess
  X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper

def frameBytes : Nat := 632

def hashOffset : Nat := 264

def bufferOffset : Nat := 392

def tailLengthOffset : Nat := 265

def blockCountOffset : Nat := 200

def blockCountHighOffset : Nat := 192

def outputSaveOffset : Nat := 624

def pointerSaveOffset : Nat := 616

def lengthSaveOffset : Nat := 608

def hashPointer (initial : RamState) (form : Form := .slices)
    (memory : ResetLayout.MemoryOffsets := form.bufferedMemory) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 memory.hash

def bufferPointer (initial : RamState) (form : Form := .slices)
    (memory : ResetLayout.MemoryOffsets := form.bufferedMemory) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 memory.buffer

def tailLengthPointer (initial : RamState) (form : Form := .slices)
    (memory : ResetLayout.MemoryOffsets := form.bufferedMemory) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 memory.tail

def blockCountPointer (initial : RamState) (form : Form := .slices)
    (memory : ResetLayout.MemoryOffsets := form.bufferedMemory) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 memory.countLow

def blockCountHighPointer (initial : RamState) (form : Form := .slices)
    (memory : ResetLayout.MemoryOffsets := form.bufferedMemory) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 memory.countHigh

def outputSavePointer (initial : RamState) (form : Form := .slices) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 form.outputSlot

def pointerSavePointer (initial : RamState) (form : Form := .slices) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 form.pointerSlot

def lengthSavePointer (initial : RamState) (form : Form := .slices) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 form.lengthSlot

theorem Variant.initialHash_size (v : Variant) : v.initialHash.size = 8 := by
  cases v <;> decide +kernel

theorem Variant.outputBytes_eq (v : Variant) : v.routine.outputBytes = v.outputBytes := by
  rfl

theorem Variant.routine_frameBytes (v : Variant) : v.routine.minStackBytes = 1184 := by
  rfl

theorem Variant.hash_data_eq_digest (v : Variant) (input : ByteArray) :
    (v.hash input).data = (v.digest input).toArray := by
  cases v
  · exact Sha2.Proofs.FIPS180.SHA512Bridge.sha384_eq_fips180 input
  · exact Sha2.Proofs.FIPS180.SHA512Bridge.sha512_eq_fips180 input
  · exact Sha2.Proofs.FIPS180.SHA512Bridge.sha512_224_eq_fips180 input
  · exact Sha2.Proofs.FIPS180.SHA512Bridge.sha512_256_eq_fips180 input

theorem Variant.hash_size (v : Variant) (input : ByteArray) :
    (v.hash input).size = v.outputBytes := by
  have h := congrArg Array.size (Variant.hash_data_eq_digest v input)
  simpa only [ByteArray.size_data, Vector.size_toArray, Variant.outputBytes] using h

theorem prefixMessage_final (inputs : Array Input) :
    prefixMessage inputs inputs.size = message inputs :=
  Sha2.Proofs.Wrapper.prefixMessage_size inputs

def Variant.outputRegion (v : Variant) (initial : RamState) (form : Form := .slices) :
    MemoryRegion :=
  match form with
  | .slices => Program.outputRegion (v.routine form) initial
  | .digest => Program.OneShot.outputRegion (v.routine form) initial
  | _ => if form.secondOutput then TwoOutputs.secondOutputRegion (v.routine form) initial
      else TwoOutputs.outputRegion (v.routine form) initial

def Variant.writeRegions (v : Variant) (initial : RamState) (form : Form := .slices) :
    Vector MemoryRegion form.writeRegionCount :=
  match form with
  | .slices | .digest =>
    #v[v.outputRegion initial form, Stack.region initial (v.routine form).minStackBytes]
  | .reset _ | .finalizeIntoReset _ | .traitFinalizeIntoReset _ =>
    #v[TwoOutputs.outputRegion (v.routine form) initial,
      TwoOutputs.secondOutputRegion (v.routine form) initial,
      Stack.region initial (v.routine form).minStackBytes]

theorem Variant.outputRegion_eq (v : Variant) (initial : RamState) (form : Form) :
    v.outputRegion initial form =
      ⟨(initial.regValue form.outputRegister).toNat, v.outputBytes⟩ := by
  cases form with
  | slices | digest => rfl
  | reset stage =>
    by_cases h : stage.val = 2 <;>
      simp [Variant.outputRegion, Form.outputRegister, Form.secondOutput, h,
        TwoOutputs.outputRegion, TwoOutputs.secondOutputRegion, registerRegion, Variant.routine]
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> rfl

theorem Variant.outputRegion_mem_writeRegions (v : Variant) (initial : RamState) (form : Form) :
    v.outputRegion initial form ∈ (v.writeRegions initial form).toList := by
  cases form with
  | slices | digest => simp [Variant.writeRegions, Form.writeRegionCount, Form.twoOutputs]
  | reset stage =>
    by_cases h : stage.val = 2 <;>
      simp [Variant.writeRegions, Variant.outputRegion, Form.secondOutput, h,
        Form.writeRegionCount, Form.twoOutputs, Vector.toList]
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;>
      simp [Variant.writeRegions, Variant.outputRegion, Form.secondOutput,
        Form.writeRegionCount, Form.twoOutputs, Vector.toList]

def Form.readRegions (form : Form) (initial : RamState) (inputs : Array Input) :
    List MemoryRegion :=
  match form with
  | .slices => Program.readRegions initial inputs
  | .digest => (inputs.map Input.region).toList
  | _ => Program.readRegions initial inputs

def Variant.ValidCall (v : Variant) (initial : RamState) (inputs : Array Input)
    (form : Form := .slices) : Prop :=
  match form with
  | .slices => Program.ValidCall (v.routine form) initial inputs
  | .digest => ∃ data : ByteArray,
      inputs = #[⟨initial.regValue .rdi, data⟩] ∧
      Program.OneShot.ValidCall (v.routine form) initial data
  | _ => TwoOutputs.ValidCall (v.routine form) initial inputs

structure Context [bindings : Bindings] (v : Variant)
    (initial : RamState) (inputs : Array Input) (form : Form := .slices) : Prop where
  stride : UnitStringStride bindings
  machine : SupportedMachine bindings initial
  call : v.ValidCall initial inputs form

theorem Context.of_root [bindings : Bindings] (v : Variant)
    {initial : RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall v.routine initial inputs) :
    Context v initial inputs := by
  exact ⟨hBindings.stringStride,
    Sha2.Proofs.Program.SupportedMachine.of_root bindings initial hMachine hBindings, hCall⟩

theorem Context.of_sha384 [bindings : Bindings] {initial : RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha384DigestSlices initial inputs) :
    Context .sha384 initial inputs := by
  apply Context.of_root .sha384 hBindings hMachine
  simpa only [Variant.routine_sha384] using hCall

theorem Context.of_sha512 [bindings : Bindings] {initial : RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha512DigestSlices initial inputs) :
    Context .sha512 initial inputs := by
  apply Context.of_root .sha512 hBindings hMachine
  simpa only [Variant.routine_sha512] using hCall

theorem Context.of_digest [bindings : Bindings] (v : Variant)
    {initial : RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall (v.routine .digest) initial data) :
    Context v initial #[⟨initial.regValue .rdi, data⟩] .digest := by
  exact ⟨hBindings.stringStride,
    Sha2.Proofs.Program.SupportedMachine.of_root bindings initial hMachine hBindings,
    data, rfl, hCall⟩

theorem Context.of_twoOutputs [bindings : Bindings] (v : Variant) (form : Form)
    (isReset : form.twoOutputs = true) {initial : RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : TwoOutputs.ValidCall (v.routine form) initial inputs) :
    Context v initial inputs form := by
  refine ⟨hBindings.stringStride,
    Sha2.Proofs.Program.SupportedMachine.of_root bindings initial hMachine hBindings, ?_⟩
  cases form with
  | slices | digest => contradiction
  | reset _ | finalizeIntoReset _ | traitFinalizeIntoReset _ => exact hCall

theorem Context.twoOutputsCall [Bindings] {v : Variant} {form : Form}
    {initial : RamState} {inputs : Array Input} (ctx : Context v initial inputs form)
    (isReset : form.twoOutputs = true) :
    TwoOutputs.ValidCall (v.routine form) initial inputs := by
  cases form with
  | slices | digest => contradiction
  | reset _ | finalizeIntoReset _ | traitFinalizeIntoReset _ => exact ctx.call

theorem Context.stack [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    {form : Form} (ctx : Context v initial inputs form) :
    Stack.Valid initial (v.routine form).minStackBytes := by
  cases form with
  | slices => exact ctx.call.stack
  | digest =>
    obtain ⟨data, _, call⟩ := ctx.call
    exact call.stack
  | reset stage =>
    exact ctx.call.stack
  | finalizeIntoReset second =>
    exact ctx.call.stack
  | traitFinalizeIntoReset second =>
    exact ctx.call.stack

theorem Context.outputInMemory [Bindings] {v : Variant} {initial : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form) :
    (v.outputRegion initial form).start ≠ 0 ∧
      (v.outputRegion initial form).Bounded ∧
      (v.outputRegion initial form).Allocated initial.external := by
  cases form with
  | slices => exact ctx.call.outputInMemory
  | digest =>
    obtain ⟨data, _, call⟩ := ctx.call
    exact call.outputInMemory
  | reset stage =>
    apply ctx.call.outputInMemory
    simp only [Variant.outputRegion]
    split <;> simp
  | finalizeIntoReset second =>
    apply ctx.call.outputInMemory
    simp only [Variant.outputRegion]
    split <;> simp
  | traitFinalizeIntoReset second =>
    apply ctx.call.outputInMemory
    simp only [Variant.outputRegion]
    split <;> simp

theorem Context.separation [Bindings] {v : Variant} {initial : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form) :
    WritableRegionsSeparated (v.writeRegions initial form).toList
      (form.readRegions initial inputs) := by
  cases form with
  | slices => exact ctx.call.separation
  | digest =>
    obtain ⟨data, rfl, call⟩ := ctx.call
    simpa [Variant.writeRegions, Variant.outputRegion, Form.readRegions,
      OneShot.MemorySeparation, OneShot.inputRegion, Input.region, registerRegion, Form.writeRegionCount, Form.twoOutputs, Vector.toList] using call.separation
  | reset stage =>
    exact ctx.call.separation
  | finalizeIntoReset second =>
    exact ctx.call.separation
  | traitFinalizeIntoReset second =>
    exact ctx.call.separation

theorem Context.returnAddress [Bindings] {v : Variant} {initial : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form) :
    ValidReturnAddress initial := by
  cases form with
  | slices => exact ctx.call.returnAddress
  | digest =>
    obtain ⟨data, _, call⟩ := ctx.call
    exact call.returnAddress
  | reset stage =>
    exact ctx.call.returnAddress
  | finalizeIntoReset second =>
    exact ctx.call.returnAddress
  | traitFinalizeIntoReset second =>
    exact ctx.call.returnAddress

theorem Context.programLoaded [Bindings] {v : Variant} {initial : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form) :
    ProgramLoaded initial := by
  cases form with
  | slices => exact ctx.call.programLoaded
  | digest =>
    obtain ⟨data, _, call⟩ := ctx.call
    exact call.programLoaded
  | reset stage =>
    exact ctx.call.programLoaded
  | finalizeIntoReset second =>
    exact ctx.call.programLoaded
  | traitFinalizeIntoReset second =>
    exact ctx.call.programLoaded

theorem Context.directionFlagUnset [Bindings] {v : Variant} {initial : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form) :
    DirectionFlagUnset initial := by
  cases form with
  | slices => exact ctx.call.directionFlagUnset
  | digest =>
    obtain ⟨data, _, call⟩ := ctx.call
    exact call.directionFlagUnset
  | reset stage =>
    exact ctx.call.directionFlagUnset
  | finalizeIntoReset second =>
    exact ctx.call.directionFlagUnset
  | traitFinalizeIntoReset second =>
    exact ctx.call.directionFlagUnset

theorem Context.inputInMemory [Bindings] {v : Variant} {initial : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form)
    (i : Fin inputs.size) :
    inputs[i].address ≠ 0 ∧ inputs[i].region.Bounded ∧
      inputs[i].region.HasBytes initial.external inputs[i].bytes := by
  cases form with
  | slices => exact ⟨(ctx.call.inputsInMemory i).1, (ctx.call.inputsInMemory i).2.2.2⟩
  | digest =>
    obtain ⟨data, rfl, call⟩ := ctx.call
    have hi : i = ⟨0, by change 0 < 1; decide⟩ := by
      apply Fin.ext
      change i.val = 0
      have h := i.isLt
      change i.val < 1 at h
      omega
    subst i
    refine ⟨?_, call.inputInMemory.2⟩
    intro zero
    apply call.inputInMemory.1
    change (initial.regValue .rdi).toNat = 0
    change initial.regValue .rdi = 0 at zero
    rw [zero]
    rfl
  | reset stage =>
    exact ⟨(ctx.call.inputsInMemory i).1, (ctx.call.inputsInMemory i).2.2.2⟩
  | finalizeIntoReset second =>
    exact ⟨(ctx.call.inputsInMemory i).1, (ctx.call.inputsInMemory i).2.2.2⟩
  | traitFinalizeIntoReset second =>
    exact ⟨(ctx.call.inputsInMemory i).1, (ctx.call.inputsInMemory i).2.2.2⟩

theorem Context.count_bound [Bindings] {v : Variant} {initial : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form) :
    inputs.size < 2^29 := by
  cases form with
  | slices => exact validCall_count_bound ctx.call
  | digest =>
    obtain ⟨data, rfl, _⟩ := ctx.call
    change 1 < 2^29
    decide
  | reset stage =>
    have h := ctx.call.pointerTableValid.2
    change (initial.regValue .rdi).toNat + 8 * inputs.size < 2^32 at h
    omega
  | finalizeIntoReset second =>
    have h := ctx.call.pointerTableValid.2
    change (initial.regValue .rdi).toNat + 8 * inputs.size < 2^32 at h
    omega
  | traitFinalizeIntoReset second =>
    have h := ctx.call.pointerTableValid.2
    change (initial.regValue .rdi).toNat + 8 * inputs.size < 2^32 at h
    omega

structure SavedStackAt (initial s : RamState) : Prop where
  words : ∀ slot ∈ ([(Syntax.Reg.rbp, 8), (.r15, 16), (.r14, 24),
      (.r13, 32), (.r12, 40), (.rbx, 48)] : List (Syntax.Reg × Nat)),
    memLoad s.external (stackPtr initial - BitVec.ofNat 64 slot.2) 64 =
      initial.regValue slot.1
  returnAddress : memLoad s.external (stackPtr initial) 64 =
    memLoad initial.external (stackPtr initial) 64

structure State [bindings : Bindings] (v : Variant)
    (initial s : RamState) (form : Form := .slices) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  machine : SupportedMachine bindings s
  loaded : ProgramLoaded s
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  saved : SavedStackAt initial s
  directionFlag : DirectionFlagUnset s
  frame : MemoryWriteFrame initial s (v.writeRegions initial form)
  rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes

theorem State.toExecutionState [Bindings] {v : Variant} {initial s : RamState}
    {form : Form} (state : State v initial s form) :
    ExecutionState initial s (v.writeRegions initial form) :=
  ⟨state.execution, state.machine, state.loaded, state.allocated,
    state.directionFlag, state.frame⟩

theorem State.of_executionState [Bindings] {v : Variant} {initial s : RamState}
    {form : Form} (state : ExecutionState initial s (v.writeRegions initial form))
    (saved : SavedStackAt initial s)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes) :
    State v initial s form :=
  ⟨state.execution, state.machine, state.loaded, state.allocated, saved,
    state.directionFlag, state.frame, rsp⟩

structure Preserved [Bindings] (v : Variant)
    (initial s : RamState) (form : Form := .slices) : Prop extends State v initial s form where
  outputPointer : match form with
    | .slices => memLoad s.external (outputSavePointer initial) 64 = initial.regValue .rcx
    | .digest => s.regValue .rbx = initial.regValue .rdx
    | _ =>
      (memLoad s.external (outputSavePointer initial form) 64 =
        initial.regValue (if form.secondOutput then .r8 else .rcx) ∨
        (form = .traitFinalizeIntoReset false ∧ s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx)) ∧
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 form.secondOutputSlot) 64 =
        initial.regValue .r8
  pointerTable : match form with
    | .digest => True
    | _ => memLoad s.external (pointerSavePointer initial form) 64 = initial.regValue .rdi
  lengthTable : match form with
    | .digest => True
    | _ => memLoad s.external (lengthSavePointer initial form) 64 = initial.regValue .rdx

def tailRegion (initial : RamState) (message : ByteArray) (form : Form := .slices)
    (memory : ResetLayout.MemoryOffsets := form.bufferedMemory) : MemoryRegion :=
  ⟨(bufferPointer initial form memory).toNat, message.size % 128⟩

def tailData (message : ByteArray) : ByteArray :=
  message.extract (128 * (message.size / 128)) message.size

structure Buffered [Bindings] (v : Variant)
    (initial s : RamState) (message : ByteArray) (form : Form := .slices)
    (memory : ResetLayout.MemoryOffsets := form.bufferedMemory) : Prop
    extends Preserved v initial s form where
  hashWords : HashStateAt s (hashPointer initial form memory)
    (compressBlocks v.initialHash message)
  tailBytes : (tailRegion initial message form memory).HasBytes s.external (tailData message)
  tailLength : s.external[tailLengthPointer initial form memory]? =
    some (UInt8.ofNat (message.size % 128))
  blockCount : memLoad s.external (blockCountPointer initial form memory) 64 =
    BitVec.ofNat 64 (message.size / 128)
  blockCountHigh : memLoad s.external (blockCountHighPointer initial form memory) 64 =
    BitVec.ofNat 64 ((message.size / 128) / 2^64)

def Variant.indexValue (v : Variant) (form : Form) (s : RamState) : BitVec 64 :=
  (.reg (BitVec.ofNat 5 (v.traversal form).indexReg) : Operand 64).read s

def Variant.countValue (v : Variant) (form : Form) (initial s : RamState) : BitVec 64 :=
  match (v.traversal form).countReg with
  | some reg => (.reg (BitVec.ofNat 5 reg) : Operand 64).read s
  | none => memLoad s.external
      (stackPtr initial - BitVec.ofNat 64 ((v.traversal form).countSlot.getD 0)) 64

def Variant.sourceValue (v : Variant) (form : Form) (s : RamState) : BitVec 64 :=
  (.reg (BitVec.ofNat 5 (v.traversal form).dataReg) : Operand 64).read s

def Variant.lengthValue (v : Variant) (form : Form) (s : RamState) : BitVec 64 :=
  (.reg (BitVec.ofNat 5 (v.traversal form).lengthReg) : Operand 64).read s

def Variant.tailValue (v : Variant) (form : Form) (s : RamState) : BitVec 64 :=
  (.reg (BitVec.ofNat 5 (v.traversal form).tailReg) : Operand 64).read s

structure LoopState [Bindings] (v : Variant)
    (initial s : RamState) (inputs : Array Input) (index : Nat) (form : Form := .slices)
    extends Buffered v initial s (prefixMessage inputs index) form where
  rip : s.RIP = v.pc (v.traversal form).head form
  indexRegister : v.indexValue form s = BitVec.ofNat 64 index
  countRegister : v.countValue form initial s = BitVec.ofNat 64 inputs.size
  remaining : index < inputs.size
  outputSaved : form = .traitFinalizeIntoReset false →
    memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx
  bufferRegister : form = .reset 1 →
    s.regValue .rbx = bufferPointer initial form
  memcpyTarget : match form with
    | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
    | .finalizeIntoReset true =>
      s.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
    | .traitFinalizeIntoReset second =>
      s.regValue (if second then .rbp else .r13) = 0x10dd60
    | _ => True
  cloneRegisters : ∀ second, form = .traitFinalizeIntoReset second →
    s.regValue .rbx = bufferPointer initial form form.activeMemory ∧
      s.regValue (if second then .r14 else .r12) = bufferPointer initial form

def Variant.serialize (v : Variant) (hash : Array UInt64) : ByteArray :=
  match v with
  | .sha384 => serializeHash (hash.extract 0 6)
  | .sha512 => serializeHash hash
  | .sha512_224 => (serializeHash hash).extract 0 28
  | .sha512_256 => (serializeHash hash).extract 0 32

structure Compressed [Bindings] (v : Variant)
    (initial s : RamState) (message : ByteArray) (form : Form := .slices) : Prop
    extends Preserved v initial s form where
  rip : s.RIP = v.pc (v.serializeOffset form) form
  digest : ∃ hash, HashStateAt s (stackPtr initial - BitVec.ofNat 64 form.finalMemory.hash) hash ∧
    v.serialize hash = v.hash message
  finalizes : form.canFinalize
  resetHashPointer : form = .reset 1 →
    s.regValue .r14 = stackPtr initial - BitVec.ofNat 64 ResetLayout.resetMemory.hash
  traitOutputPointer : form = .traitFinalizeIntoReset false →
    s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx

theorem Buffered.tailBytes_size [Bindings] {v : Variant} {initial s : RamState}
    {message : ByteArray} {form : Form} {memory : ResetLayout.MemoryOffsets} (_state : Buffered v initial s message form memory) :
    (tailData message).size = message.size % 128 := by
  simp only [tailData, ByteArray.size_extract, Nat.min_self]
  omega

theorem Buffered.tailRegion_bounded [Bindings] {v : Variant} {initial s : RamState}
    {message : ByteArray} {form : Form} {memory : ResetLayout.MemoryOffsets} (_state : Buffered v initial s message form memory) :
    (tailRegion initial message form memory).size = (tailData message).size := by
  simp only [tailRegion, tailData, ByteArray.size_extract, Nat.min_self]
  omega

theorem Buffered.message_size_mod [Bindings] {v : Variant} {initial s : RamState}
    {message : ByteArray} {form : Form} {memory : ResetLayout.MemoryOffsets} (state : Buffered v initial s message form memory) :
    (tailData message).size < 128 := by
  rw [state.tailBytes_size]
  omega

theorem Context.prefixMessage_bound [Bindings] {v : Variant} {initial : RamState}
    {inputs : Array Input} {form : Form} (ctx : Context v initial inputs form)
    {count : Nat} (within : count ≤ inputs.size) :
    (prefixMessage inputs count).size ≤ count * (2^32 - 1) := by
  induction count with
  | zero => simp [prefixMessage_zero]
  | succ count ih =>
    rw [prefixMessage_succ inputs count (by omega), ByteArray.size_append, Nat.succ_mul]
    have prefixBound := ih (by omega)
    have current := (ctx.inputInMemory ⟨count, by omega⟩).2.1
    change inputs[count].address.toNat + inputs[count].bytes.size < 2^32 at current
    omega

theorem LoopState.prefix_size [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {index : Nat} {form : Form} (ctx : Context v initial inputs form)
    (state : LoopState v initial s inputs index form) :
    (prefixMessage inputs index).size ≤ index * (2^32 - 1) := by
  exact ctx.prefixMessage_bound (Nat.le_of_lt state.remaining)

theorem LoopState.block_count_high_zero [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {index : Nat} {form : Form} (ctx : Context v initial inputs form)
    (state : LoopState v initial s inputs index form) :
    (message (inputs.extract 0 index)).size / 128 / 2^64 = 0 := by
  change (prefixMessage inputs index).size / 128 / 2^64 = 0
  have hremaining := state.remaining
  have hprefix := ctx.prefixMessage_bound (Nat.le_of_lt state.remaining)
  have hsize : (prefixMessage inputs index).size ≤ index * (2^32 - 1) := hprefix
  have hcount := ctx.count_bound
  have hindex : index < 2^29 := by
    omega
  have hquotient : (prefixMessage inputs index).size / 128 < 2^64 := by
    omega
  exact Nat.div_eq_of_lt hquotient

theorem LoopState.next_message [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} {index : Nat} {form : Form} (_state : LoopState v initial s inputs index form)
    (hi : index < inputs.size) :
    prefixMessage inputs (index + 1) =
      prefixMessage inputs index ++ inputs[index].bytes := by
  exact prefixMessage_succ inputs index hi

theorem Compressed.serialized_hash [Bindings] {v : Variant} {initial s : RamState}
    {message : ByteArray} {form : Form} (state : Compressed v initial s message form) :
    ∃ hash, hash.size = 8 ∧
      v.serialize hash = v.hash message := by
  obtain ⟨hash, hstate, hserialized⟩ := state.digest
  exact ⟨hash, hstate.1, hserialized⟩

end Sha2.Proofs.Wrapper512
