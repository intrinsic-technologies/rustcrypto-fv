import Sha2.Proofs.Common.SHA256.Instances.Digest.Saved
import Sha2.Proofs.Common.SHA256.Instances.Digest.Return
import Sha2.Proofs.Common.Memory.ReadOutput

namespace Sha2.Proofs.OneShot

open Sha2.Spec Sha2.Spec.Program Standards.NIST.SHA2 Prelude X86

theorem correct_variant {v : Wrapper.Variant}
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall (Common.SHA256.Instances.Digest.routine v) initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion (Common.SHA256.Instances.Digest.routine v) initial,
          Stack.region initial (Common.SHA256.Instances.Digest.routine v).minStackBytes] ∧
      OneShot.readOutput (Common.SHA256.Instances.Digest.routine v) initial final = .ok (v.digest data) := by
  let machine := Sha2.Proofs.Program.SupportedMachine.of_root bindings initial hMachine hBindings
  obtain ⟨p, h, u, absorbedState, push, prsp, args, init, input⟩ :=
    Common.SHA256.Instances.Digest.absorbed (v := v) hBindings.stringStride machine hCall
  have hasher : Common.SHA256.HasherAt absorbedState (X86Proofs.rspOf absorbedState + 168) data v.initialHash := by
    have rsp : X86Proofs.rspOf absorbedState = (Common.SHA256.Instances.Digest.absorb v).sp initial := input.rsp
    rw [rsp]
    exact input.hasher
  obtain ⟨c, q, t, stateT, setup, copy, normalize, prepared⟩ :=
    Common.SHA256.Instances.Digest.cloned (v := v) hBindings.stringStride machine hCall
      input.state (input.rip.trans (by cases v <;> rfl)) input.rsp hasher
  obtain ⟨z, finished⟩ := Common.SHA256.Instances.Digest.finalized (v := v)
    hBindings.stringStride machine hCall stateT prepared
  have ptr := Common.SHA256.Instances.Digest.pointers (v := v) push args init input setup copy normalize finished
  obtain ⟨a, w, stateW, load, store, bytes⟩ :=
    Common.SHA256.Instances.Digest.serialized (v := v) machine hCall finished ptr.1
  have output : (X86Proofs.Operand.reg 3 : X86Proofs.Operand 64).read a = initial.regValue .rdx :=
    (load.agrees.read (n := 64) (r := 3) (by
      cases v <;> simp [Common.SHA256.Serialize.effect, X86Proofs.Effect.components])).trans ptr.1
  have memory := Common.SHA256.Instances.Digest.saved_memory (v := v) hCall prsp args init input
    setup copy normalize finished load store output
  have rsp : X86Proofs.rspOf w = X86Proofs.stackPtr initial - 312 :=
    (store.agrees.read (n := 64) (r := 4) (by
      cases v <;> simp [Common.SHA256.Serialize.effect, X86Proofs.Effect.components])).trans
      ((load.agrees.read (n := 64) (r := 4) (by
        cases v <;> simp [Common.SHA256.Serialize.effect, X86Proofs.Effect.components])).trans finished.rsp)
  have rbp : w.regValue .rbp = initial.regValue .rbp :=
    (store.agrees.read (n := 64) (r := 5) (by
      cases v <;> simp [Common.SHA256.Serialize.effect, X86Proofs.Effect.components])).trans
      ((load.agrees.read (n := 64) (r := 5) (by
        cases v <;> simp [Common.SHA256.Serialize.effect, X86Proofs.Effect.components])).trans ptr.2)
  obtain ⟨fuel, final, unique, finalMachine, abi, direction, frame, finalMemory⟩ :=
    Common.SHA256.Instances.Digest.returned (v := v) machine hCall push stateW rsp (by
      have nextPC : (Common.SHA256.Instances.Digest.Segment.store.pc v) +
          BitVec.ofNat 64 (Common.SHA256.Serialize.bytes (.store .rbx (v == .sha224))).length =
          Common.SHA256.Instances.Digest.Segment.epilogue.pc v := by cases v <;> decide +kernel
      exact nextPC ▸ store.rip) rbp memory
  refine ⟨fuel, final, unique, finalMachine.supported,
    finalMachine.to_environment hBindings.stringStride, abi, direction, frame, ?_⟩
  cases v with
  | sha224 =>
    apply Common.Memory.readBytes_of_hasBytes
    rw [finalMemory]
    exact bytes
  | sha256 =>
    apply Common.Memory.readBytes_sha256
    rw [finalMemory]
    exact bytes

theorem correct
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha256Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha256Digest initial,
          Stack.region initial sha256Digest.minStackBytes] ∧
      OneShot.readOutput sha256Digest initial final = .ok (SHA256 (bytesToBits data)).bytes := by
  exact correct_variant (v := .sha256) hBindings hMachine hCall

end Sha2.Proofs.OneShot

namespace Sha2.Statements

open Sha2.Spec Sha2.Spec.Program Standards.NIST.SHA2 Prelude X86

theorem sha224_digest_writes_sha224_of_data
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : OneShot.ValidCall sha224Digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[OneShot.outputRegion sha224Digest initial,
          Stack.region initial sha224Digest.minStackBytes] ∧
      OneShot.readOutput sha224Digest initial final = .ok (SHA224 (bytesToBits data)).bytes := by
  exact Sha2.Proofs.OneShot.correct_variant (v := .sha224) hBindings hMachine hCall

end Sha2.Statements
