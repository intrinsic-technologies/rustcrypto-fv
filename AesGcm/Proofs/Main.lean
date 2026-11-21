import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Aes256.Execution
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256.Authenticated
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256.Prefix
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Execution
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Authenticated
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Prefix
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Result
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Finish
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.ValidCall
import AesGcm.Proofs.Machine.Runtime.Root.Program
import AesGcm.Proofs.Machine.Runtime.Root.Output
import AesGcm.Proofs.Machine.Runtime.Execution
import AesGcm.Spec
import AesGcm.Proofs.Common.ResultMatcher

namespace AesGcm.Statements

open AesGcm.Spec AesGcm.Spec.Program Prelude X86
open X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs AesGcm.Proofs.Machine AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

theorem aes128gcm_decrypt_in_place_writes_plaintext_or_rejects
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 16} {nonce : Vector UInt8 12}
    {associatedData sealed : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : InPlace.ValidCall aes128gcmDecryptInPlace initial key nonce
      associatedData sealed sealed.size sealed.size) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      aes128gcm_decrypt_in_place_writes_plaintext_or_rejects.match_1 (fun _ => Prop)
        (GCM.authenticPlaintextOfCiphertextWithTag .aes128 key nonce associatedData sealed)
        (fun plaintext =>
          SuccessfulStatus final ∧
          MemoryWriteFrame initial final
            #v[InPlace.outputRegion initial (sealed.size - 16),
              Stack.region initial aes128gcmDecryptInPlace.minStackBytes] ∧
          InPlace.readOutput initial final (sealed.size - 16) = .ok plaintext)
        (fun _ =>
          FailureStatus final 1 ∧
          MemoryWriteFrame initial final
            #v[Stack.region initial aes128gcmDecryptInPlace.minStackBytes]) := by
  obtain ⟨ret, hframe⟩ := entryFrame hCall
  let fr := Activation.ofEntry initial aes128gcmDecryptInPlace.minStackBytes ret
  let pc : LIR.Label := .l101240
  let result := GCM.authenticPlaintextOfCiphertextWithTag .aes128 key nonce associatedData sealed
  have hentry : Rel Extracted.programImage LIR.lifted
      ⟨LIR.lifted.locationOf pc initial, []⟩ initial :=
    root_lifted_entry hMachine hBindings hCall.programLoaded (fun _ h => h) hCall.entry
  have near := nearReturn64Boundary_eq initial hentry.ready.dataReady hMachine.integer.ss
    hframe.memReadable
  have sim := root_simulation hBindings (boundary := returnBoundary initial) (by
    intro hp
    exact hframe.retOutside _ hp.choose_spec (by exact hframe.returnBoundary.1))
  obtain ⟨output, execution, htag, hdone, hpost⟩ :
      ∃ output, LIR.program.Exec (dialect Extracted.programImage)
        ⟨LIR.lifted.locationOf pc initial, []⟩ output ∧
        resultPost Extracted.programImage fr (sealed.size - 16)
          result output := by
    obtain ⟨args, mem, reaches, hinit⟩ := reaches_length_check hCall hframe
    by_cases hsize : 16 ≤ sealed.size
    · obtain ⟨out, exec, post⟩ := exec_with_tag hCall hframe args mem hinit hsize
      exact ⟨out, Program.Exec.of_sem (reaches.exec exec.sem), post⟩
    · obtain ⟨working, _, _, hw, typed⟩ := hinit
      have hshort : fr.r9.toNat < 16 := by
        change (initial.regValue .r9).toNat < 16
        rw [hCall.lengthArgumentMatchesBuffer]
        omega
      obtain ⟨out, exec, htag, doneAtoms, _, hmem, hstatus⟩ :=
        reject_exec false Extracted.programImage fr args mem typed working hshort
      refine ⟨out, Program.Exec.of_sem (reaches.exec exec.sem), htag, doneAtoms, ?_⟩
      simp only [result, GCM.authenticPlaintextOfCiphertextWithTag, dite_eq_right hsize]
      exact ⟨hstatus, hmem ▸ hw⟩
  have hsp : output.values[4] = ⟨64, (returnBoundary initial).rsp⟩ := by
    rw [hframe.returnBoundary.2]
    exact hdone.1
  obtain ⟨fuel, final, hu, hm, hb, hr⟩ := run_of_lifted_execution hBindings near sim
    hentry execution (hframe.returnBoundary.1 ▸ htag) hsp (by decide)
  obtain ⟨hcallee, hdf⟩ := calleeSaved_of_doneAtoms hframe hr hdone rfl
    (by decide) (by decide)
  refine ⟨fuel, final, hu, hm, hb, hcallee, hdf, ?_⟩
  have hrax : output.values[0] = ⟨64, final.regValue .rax⟩ := hr.regs 0 (by decide) (by decide)
  change aes128gcm_decrypt_in_place_writes_plaintext_or_rejects.match_1 (fun _ => Prop) result _ _
  cases hmodel : result with
  | none =>
    rw [hmodel] at hpost
    obtain ⟨status, frame⟩ := hpost
    rw [hr.store] at frame
    refine ⟨?_, frame.memoryWriteFrame ?_⟩
    · have he := Value.eq_bits (hrax.symm.trans status)
      exact congrArg (BitVec.setWidth 32) he
    · intro x hx r hrgn
      rcases List.mem_singleton.mp hrgn with rfl
      exact fun hc => hx _ (by simp) (Activation.ofEntry_region_within x hc)
  | some plaintext =>
    rw [hmodel] at hpost
    obtain ⟨status, frame, bytes⟩ := hpost
    rw [hr.store] at frame bytes
    refine ⟨?_, frame.memoryWriteFrame ?_, inplace_readOutput_of_hasBytes bytes⟩
    · have he := Value.eq_bits (hrax.symm.trans status)
      exact congrArg (BitVec.setWidth 32) he
    · intro x hx r hrgn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrgn
      rcases hrgn with rfl | rfl
      · exact fun hc => hx _ (by simp) (Activation.ofEntry_region_within x hc)
      · exact hx (InPlace.outputRegion initial (sealed.size - 16)) (by simp)

open AesGcm.Proofs.Machine.Entry.InPlaceEncrypt (execute entryActivation stack_contains)

theorem aes128gcm_encrypt_in_place_writes_ciphertext_and_tag_or_fails_without_room
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 16} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray} {capacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : InPlace.ValidCapacityCall aes128gcmEncryptInPlace initial key nonce
      associatedData plaintext capacity) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match GCM.ciphertextAndTag .aes128 key nonce associatedData plaintext with
      | some (ciphertext, tag) =>
        if plaintext.size + 16 ≤ capacity then
          SuccessfulStatus final ∧
          MemoryWriteFrame initial final
            #v[InPlace.outputRegion initial (plaintext.size + 16),
              Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16] ∧
          InPlace.readOutput initial final (plaintext.size + 16) =
            .ok (ciphertext ++ ⟨tag.toArray⟩)
        else
          FailureStatus final 1 ∧
          MemoryWriteFrame initial final
            #v[InPlace.outputRegion initial plaintext.size,
              Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16] ∧
          InPlace.readOutput initial final plaintext.size = .ok ciphertext
      | none =>
        FailureStatus final 1 ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16] := by
  obtain ⟨fuel, final, ret, ciphertext, tag, hu, hm, hb, hcallee, hdf, model, eax, frame, bytes⟩ :=
    execute hBindings hMachine (Or.inl hCall)
  refine ⟨fuel, final, hu, hm, hb, hcallee, hdf, ?_⟩
  rw [model]
  rw [hCall.lengthArgumentMatchesBuffer] at eax frame bytes
  have hframe {n : Nat} (h : RamWriteFrame initial.external final.external
      [(entryActivation initial ret).region,
        InPlace.outputRegion initial n]) :
      MemoryWriteFrame initial final
        #v[InPlace.outputRegion initial n, Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16] := by
    apply h.memoryWriteFrame
    intro x hx r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fun hc => hx _ (by simp) (stack_contains hc)
    · exact hx _ (by simp)
  by_cases room : plaintext.size + 16 ≤ capacity
  · simp only [room, ite_true] at eax frame bytes ⊢
    exact ⟨congrArg (BitVec.setWidth 32) eax, hframe frame, inplace_readOutput_of_hasBytes bytes⟩
  · simp only [room, ite_false] at eax frame bytes ⊢
    exact ⟨congrArg (BitVec.setWidth 32) eax, hframe frame, inplace_readOutput_of_hasBytes bytes⟩

private theorem encrypt256_stack_contains {initial : Machine.RamState} {ret : BitVec 64} {x : Nat}
    (hx : (Activation.ofEntry initial aes256gcmEncryptInPlace.minStackBytes ret).region.Contains x) :
    (Stack.region initial aes256gcmEncryptInPlace.minStackBytes 16).Contains x := by
  have h := Activation.ofEntry_region_within x hx
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains] at h ⊢
  omega

theorem aes256gcm_encrypt_in_place_writes_ciphertext_and_tag_or_fails_without_room
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray} {capacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : InPlace.ValidCapacityCall aes256gcmEncryptInPlace initial key nonce
      associatedData plaintext capacity) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match GCM.ciphertextAndTag .aes256 key nonce associatedData plaintext with
      | some (ciphertext, tag) =>
        if plaintext.size + 16 ≤ capacity then
          SuccessfulStatus final ∧
          MemoryWriteFrame initial final
            #v[InPlace.outputRegion initial (plaintext.size + 16),
              Stack.region initial aes256gcmEncryptInPlace.minStackBytes 16] ∧
          InPlace.readOutput initial final (plaintext.size + 16) =
            .ok (ciphertext ++ ⟨tag.toArray⟩)
        else
          FailureStatus final 1 ∧
          MemoryWriteFrame initial final
            #v[InPlace.outputRegion initial plaintext.size,
              Stack.region initial aes256gcmEncryptInPlace.minStackBytes 16] ∧
          InPlace.readOutput initial final plaintext.size = .ok ciphertext
      | none =>
        FailureStatus final 1 ∧
        MemoryWriteFrame initial final
          #v[Stack.region initial aes256gcmEncryptInPlace.minStackBytes 16] := by
  obtain ⟨fuel, final, ret, ciphertext, tag, hu, hm, hb, hcallee, hdf, model, eax, frame, bytes⟩ :=
    AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Aes256.execute hBindings hMachine (Or.inl hCall)
  refine ⟨fuel, final, hu, hm, hb, hcallee, hdf, ?_⟩
  rw [model]
  rw [hCall.lengthArgumentMatchesBuffer] at eax frame bytes
  have hframe {n : Nat} (h : RamWriteFrame initial.external final.external
      [(Activation.ofEntry initial aes256gcmEncryptInPlace.minStackBytes ret).region,
        InPlace.outputRegion initial n]) :
      MemoryWriteFrame initial final
        #v[InPlace.outputRegion initial n, Stack.region initial aes256gcmEncryptInPlace.minStackBytes 16] := by
    apply h.memoryWriteFrame
    intro x hx r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fun hc => hx _ (by simp) (encrypt256_stack_contains hc)
    · exact hx _ (by simp)
  by_cases room : plaintext.size + 16 ≤ capacity
  · simp only [room, ite_true] at eax frame bytes ⊢
    exact ⟨congrArg (BitVec.setWidth 32) eax, hframe frame, inplace_readOutput_of_hasBytes bytes⟩
  · simp only [room, ite_false] at eax frame bytes ⊢
    exact ⟨congrArg (BitVec.setWidth 32) eax, hframe frame, inplace_readOutput_of_hasBytes bytes⟩

theorem aes256gcm_decrypt_in_place_writes_plaintext_or_rejects
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData sealed : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : InPlace.ValidCall aes256gcmDecryptInPlace initial key nonce
      associatedData sealed sealed.size sealed.size) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      aes128gcm_decrypt_in_place_writes_plaintext_or_rejects.match_1 (fun _ => Prop)
        (GCM.authenticPlaintextOfCiphertextWithTag .aes256 key nonce associatedData sealed)
        (fun plaintext =>
          SuccessfulStatus final ∧
          MemoryWriteFrame initial final
            #v[InPlace.outputRegion initial (sealed.size - 16),
              Stack.region initial aes256gcmDecryptInPlace.minStackBytes] ∧
          InPlace.readOutput initial final (sealed.size - 16) = .ok plaintext)
        (fun _ =>
          FailureStatus final 1 ∧
          MemoryWriteFrame initial final
            #v[Stack.region initial aes256gcmDecryptInPlace.minStackBytes]) := by
  obtain ⟨ret, hframe⟩ := AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256.entryFrame hCall
  let fr := Activation.ofEntry initial aes256gcmDecryptInPlace.minStackBytes ret
  let pc : LIR.Label := .l101520
  let result := GCM.authenticPlaintextOfCiphertextWithTag .aes256 key nonce associatedData sealed
  have hentry : Rel Extracted.programImage LIR.lifted
      ⟨LIR.lifted.locationOf pc initial, []⟩ initial :=
    root_lifted_entry hMachine hBindings hCall.programLoaded (fun _ h => h) hCall.entry
  have near := nearReturn64Boundary_eq initial hentry.ready.dataReady hMachine.integer.ss
    hframe.memReadable
  have sim := root_simulation hBindings (boundary := returnBoundary initial) (by
    intro hp
    exact hframe.retOutside _ hp.choose_spec (by exact hframe.returnBoundary.1))
  obtain ⟨output, execution, htag, hdone, hpost⟩ :
      ∃ output, LIR.program.Exec (dialect Extracted.programImage)
        ⟨LIR.lifted.locationOf pc initial, []⟩ output ∧
        resultPost Extracted.programImage fr (sealed.size - 16)
          result output := by
    obtain ⟨args, mem, reaches, hinit⟩ := AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256.reaches_length_check hCall hframe
    by_cases hsize : 16 ≤ sealed.size
    · obtain ⟨out, exec, post⟩ := AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Aes256.exec_with_tag hCall hframe args mem hinit hsize
      exact ⟨out, Program.Exec.of_sem (reaches.exec exec.sem), post⟩
    · obtain ⟨working, _, _, hw, typed⟩ := hinit
      have hshort : fr.r9.toNat < 16 := by
        change (initial.regValue .r9).toNat < 16
        rw [hCall.lengthArgumentMatchesBuffer]
        omega
      obtain ⟨out, exec, htag, doneAtoms, _, hmem, hstatus⟩ :=
        reject_exec true Extracted.programImage fr args mem typed working hshort
      refine ⟨out, Program.Exec.of_sem (reaches.exec exec.sem), htag, doneAtoms, ?_⟩
      simp only [result, GCM.authenticPlaintextOfCiphertextWithTag, dite_eq_right hsize]
      exact ⟨hstatus, hmem ▸ hw⟩
  have hsp : output.values[4] = ⟨64, (returnBoundary initial).rsp⟩ := by
    rw [hframe.returnBoundary.2]
    exact hdone.1
  obtain ⟨fuel, final, hu, hm, hb, hr⟩ := run_of_lifted_execution hBindings near sim
    hentry execution (hframe.returnBoundary.1 ▸ htag) hsp (by decide)
  obtain ⟨hcallee, hdf⟩ := calleeSaved_of_doneAtoms hframe hr hdone rfl
    (by decide) (by decide)
  refine ⟨fuel, final, hu, hm, hb, hcallee, hdf, ?_⟩
  have hrax : output.values[0] = ⟨64, final.regValue .rax⟩ := hr.regs 0 (by decide) (by decide)
  change aes128gcm_decrypt_in_place_writes_plaintext_or_rejects.match_1 (fun _ => Prop) result _ _
  cases hmodel : result with
  | none =>
    rw [hmodel] at hpost
    obtain ⟨status, frame⟩ := hpost
    rw [hr.store] at frame
    refine ⟨?_, frame.memoryWriteFrame ?_⟩
    · have he := Value.eq_bits (hrax.symm.trans status)
      exact congrArg (BitVec.setWidth 32) he
    · intro x hx r hrgn
      rcases List.mem_singleton.mp hrgn with rfl
      exact fun hc => hx _ (by simp) (Activation.ofEntry_region_within x hc)
  | some plaintext =>
    rw [hmodel] at hpost
    obtain ⟨status, frame, bytes⟩ := hpost
    rw [hr.store] at frame bytes
    refine ⟨?_, frame.memoryWriteFrame ?_, inplace_readOutput_of_hasBytes bytes⟩
    · have he := Value.eq_bits (hrax.symm.trans status)
      exact congrArg (BitVec.setWidth 32) he
    · intro x hx r hrgn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrgn
      rcases hrgn with rfl | rfl
      · exact fun hc => hx _ (by simp) (Activation.ofEntry_region_within x hc)
      · exact hx (InPlace.outputRegion initial (sealed.size - 16)) (by simp)

end AesGcm.Statements
