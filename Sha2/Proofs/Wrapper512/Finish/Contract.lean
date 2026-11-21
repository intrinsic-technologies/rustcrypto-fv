import Sha2.Proofs.Wrapper512.API
import Sha2.Proofs.Wrapper512.Finish.Serialize

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Finish

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Wrapper512

 theorem readOutput_of_hasBytes {v : Variant} {form : Form} {initial final : RamState}
    {digest : Vector UInt8 v.outputBytes}
    (bytes : (v.outputRegion initial form).HasBytes final.external ⟨digest.toArray⟩) :
    v.readOutput initial final form = .ok digest := by
  have region : v.outputRegion initial form =
      ⟨(initial.regValue form.outputRegister).toNat, v.outputBytes⟩ := by
    exact v.outputRegion_eq initial form
  rw [region] at bytes
  have read (j : Fin v.outputBytes) :
      final.external[BitVec.ofNat 64 ((initial.regValue
        form.outputRegister).toNat + j.val)]? = some digest[j.val] :=
    bytes.2 ⟨j.val, by simpa only [ByteArray.size, Vector.size_toArray] using j.isLt⟩
  have result : (Vector.ofFnM (fun j : Fin v.outputBytes =>
      let a := BitVec.ofNat 64 ((initial.regValue
        form.outputRegister).toNat + j.val)
      match final.external[a]? with
      | some byte => Except.ok byte
      | none => Except.error (Fault.unmappedMemory a))) = .ok digest := by
    simp only [read]
    change Vector.ofFnM (fun j : Fin v.outputBytes => pure digest[j.val]) =
      (pure digest : Except Fault (Vector UInt8 v.outputBytes))
    rw [Vector.ofFnM_pure, Vector.ofFn_getElem]
  cases form with
  | slices | digest => exact result
  | reset stage =>
    obtain ⟨n, hn⟩ := stage
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> exact result
  | finalizeIntoReset second =>
    cases second <;> exact result
  | traitFinalizeIntoReset second =>
    cases second <;> exact result

theorem hash_eq_digest (v : Variant) (input : ByteArray) :
    v.hash input = ⟨(v.digest input).toArray⟩ := by
  apply ByteArray.ext
  exact Variant.hash_data_eq_digest v input

set_option maxHeartbeats 1000000 in
theorem result_of_state [Bindings] {v : Variant} {form : Form} {initial s final : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    (input : Compressed v initial s (message inputs) form)
    (state : State v initial final form)
    (execution : ∃ fuel, UniqueExecution initial fuel final)
    (calleeSaved : CalleeSavedRegistersUnchanged initial final)
    (hash : Array UInt64) (hsize : hash.size = 8)
    (serialized : v.serialize hash =
      v.hash (message inputs))
    (words : ∀ j, 8 * (j + 1) ≤ v.outputBytes →
      memLoad final.external (initial.regValue form.outputRegister + BitVec.ofNat 64 (8 * j)) 64 =
        Common.Instructions.bswap64 hash[j]!.toBitVec)
    (tailBytes : v = .sha512_224 → ∀ i < 4,
      final.external[initial.regValue form.outputRegister + BitVec.ofNat 64 (24 + i)]? =
        some (storedByte (Common.Instructions.bswap64 hash[3]!.toBitVec) i)) :
    FinishResult v initial final inputs form := by
  have bytes := Serialize.compressed_output ctx input state hsize serialized words tailBytes
  rw [hash_eq_digest v (message inputs)] at bytes
  refine ⟨execution, state.machine.supported, state.machine.to_environment ctx.stride,
    state.frame, ?_, calleeSaved, state.directionFlag⟩
  exact readOutput_of_hasBytes bytes

theorem finishContract [Bindings] {v : Variant} {form : Form}
    (run : ∀ {initial s : RamState} {inputs : Array Input},
      Context v initial inputs form → Buffered v initial s (message inputs) form →
        s.RIP = v.pc (v.dispatchOffset form inputs.isEmpty) form → ∃ final, FinishResult v initial final inputs form) :
    FinishContract v form :=
  ⟨run⟩

end Sha2.Proofs.Wrapper512.Finish
