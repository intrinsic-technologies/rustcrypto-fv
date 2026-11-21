import ChaCha20Poly1305.Spec
import ChaCha20Poly1305.Proofs.CoreContract
import ChaCha20Poly1305.Proofs.Wrapper
import ChaCha20Poly1305.Proofs.Decrypt.EmptyResult
import ChaCha20Poly1305.Proofs.Decrypt.ShortResult
import ChaCha20Poly1305.Proofs.Decrypt.LongResult
import ChaCha20Poly1305.Proofs.Common.ResultMatcher
import ChaCha20Poly1305.Proofs.DecryptInPlace.LengthBranch
import ChaCha20Poly1305.Proofs.DecryptInPlace.CallSetup
import ChaCha20Poly1305.Proofs.DecryptInPlace.CalleeABI
import ChaCha20Poly1305.Proofs.DecryptInPlace.CalleeInputs
import ChaCha20Poly1305.Proofs.DecryptInPlace.CalleeRun
import ChaCha20Poly1305.Proofs.DecryptInPlace.ReturnResult





namespace ChaCha20Poly1305.Statements

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86



theorem chacha20poly1305_decrypt_writes_plaintext_or_rejects_tag
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData ciphertextWithTag : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall decrypt initial [key, nonce, associatedData, ciphertextWithTag]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      chacha20poly1305_decrypt_writes_plaintext_or_rejects_tag.match_1
        (fun _ => Prop) (AEAD.decryptWithTag associatedData key nonce ciphertextWithTag)
        (fun plaintext =>
          SuccessfulStatus final ∧
          MemoryWriteFrame initial final
            #v[outputRegion decrypt initial,
              heapRegion decrypt initial, allocatorStateRegion,
              Stack.region initial decrypt.minStackBytes] ∧
          readOutput decrypt initial final = .ok plaintext)
        (fun _ =>
          FailureStatus final aeadErrorStatus ∧
          MemoryWriteFrame initial final
            #v[heapRegion decrypt initial, allocatorStateRegion,
              Stack.region initial decrypt.minStackBytes]) := by
  by_cases hEmpty : ciphertextWithTag.size = 0
  · rw [show AEAD.decryptWithTag associatedData key nonce ciphertextWithTag = none by
      simp [AEAD.decryptWithTag, hEmpty]]
    exact ChaCha20Poly1305.Proofs.Decrypt.emptyInput hBindings hMachine hCall hEmpty
  · by_cases hshort : ciphertextWithTag.size < 16
    · rw [show AEAD.decryptWithTag associatedData key nonce ciphertextWithTag = none by
        simp [AEAD.decryptWithTag, Nat.not_le.mpr hshort]]
      exact ChaCha20Poly1305.Proofs.Decrypt.shortInput hBindings hMachine hCall (Nat.pos_of_ne_zero hEmpty) hshort
    · exact ChaCha20Poly1305.Proofs.Decrypt.longInput hBindings hMachine hCall (Nat.le_of_not_lt hshort)


theorem chacha20poly1305_encrypt_in_place_writes_ciphertext_with_tag_or_rejects_buffer_without_room
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall encryptInPlace initial [key, nonce, associatedData, plaintext]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      if hasRoom encryptInPlace initial then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion encryptInPlace initial,
            Stack.region initial encryptInPlace.minStackBytes] ∧
        readOutput encryptInPlace initial final =
          .ok (AEAD.encryptWithTag associatedData key nonce plaintext)
      else
        FailureStatus final aeadErrorStatus ∧
        MemoryWriteFrame initial final
          #v[outputRegion encryptInPlace initial,
            Stack.region initial encryptInPlace.minStackBytes] ∧
        readOutput encryptInPlace initial final =
          .ok (AEAD.encryptWithoutTag associatedData key nonce plaintext) := by
  exact ChaCha20Poly1305.Proofs.Wrapper.encrypt_in_place hBindings hMachine hCall



attribute [local irreducible] ChaCha20Poly1305.Proofs.Decrypt.Detached.Packet.good Standards.RFC.ChaCha20Poly1305.poly1305Mac
  Standards.RFC.ChaCha20Poly1305.poly1305KeyGen Standards.RFC.ChaCha20Poly1305.chacha20Encrypt

open ChaCha20Poly1305.Proofs.DecryptInPlace ChaCha20Poly1305.Proofs.Decrypt ChaCha20Poly1305.Proofs.Refine in
set_option maxHeartbeats 650000 in
theorem chacha20poly1305_decrypt_in_place_writes_plaintext_or_rejects_tag
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData ciphertextWithTag : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall decryptInPlace initial [key, nonce, associatedData, ciphertextWithTag]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      chacha20poly1305_decrypt_writes_plaintext_or_rejects_tag.match_1
        (fun _ => Prop) (AEAD.decryptWithTag associatedData key nonce ciphertextWithTag)
        (fun plaintext =>
          SuccessfulStatus final ∧
          MemoryWriteFrame initial final
            #v[outputRegion decryptInPlace initial,
              Stack.region initial decryptInPlace.minStackBytes] ∧
          readOutput decryptInPlace initial final = .ok plaintext)
        (fun _ =>
          FailureStatus final aeadErrorStatus ∧
          MemoryWriteFrame initial final
            #v[Stack.region initial decryptInPlace.minStackBytes]) := by
  obtain ⟨n,u,entry,start⟩ := lengthBranch hBindings hMachine hCall
  by_cases short : ciphertextWithTag.size < 16
  · obtain ⟨k,t,unique,machine,bindings',saved,df,_,status,frame⟩ :=
      finish hBindings hMachine hCall entry (shortEpilogue hMachine hCall short start)
    rw [show AEAD.decryptWithTag associatedData key nonce ciphertextWithTag = none by
      simp [AEAD.decryptWithTag,Nat.not_le.mpr short]]
    exact ⟨k,t,unique,machine,bindings',saved,df,status,frame⟩
  · have long := Nat.le_of_not_gt short
    have bound : (initial.regValue .rcx).toNat + ciphertextWithTag.size < 2^32 :=
      hCall.inputsInMemory.2.2.2.1.1
    have small : ciphertextWithTag.size < 2^32 := by omega
    let p := inPlacePacket initial key nonce associatedData ciphertextWithTag long small
    obtain ⟨_,v,setup,atCall⟩ := callSetup hCall long small start
    obtain ⟨_,w,core,resume,data⟩ := calleeRun hBindings hMachine hCall long small atCall
      ((Atom.all_append _ _).2 ⟨calleeABI hCall long small atCall, calleeInputs hCall long small atCall⟩)
    obtain ⟨k,t,unique,machine,env,saved,df,mem,status,frame⟩ :=
      finish hBindings hMachine hCall ((entry.trans setup).trans core) resume
    refine ⟨k,t,unique,machine,env,saved,df,?_⟩
    rw [show AEAD.decryptWithTag associatedData key nonce ciphertextWithTag =
      (if p.good then some p.plain else none) from ChaCha20Poly1305.Proofs.Decrypt.Wrapper.decryptPacket]
    change (t.regValue .rax).setWidth 32 = (if p.good then 0 else 1) at status
    change (if p.good then MemoryWriteFrame initial t #v[outputRegion decryptInPlace initial,
      Stack.region initial decryptInPlace.minStackBytes] else MemoryWriteFrame initial t
      #v[Stack.region initial decryptInPlace.minStackBytes]) at frame
    cases good : p.good
    · simp only [Bool.false_eq_true,ite_false]
      exact ⟨by simpa only [FailureStatus,aeadErrorStatus,good,Bool.false_eq_true,ite_false] using status,
        by simpa only [good,Bool.false_eq_true,ite_false] using frame⟩
    · simp only [ite_true]
      have fr := resume.frame
      change RamWriteFrame _ _ (footprint initial p.good) at fr
      rw [good,←mem] at fr
      exact ⟨by simpa only [SuccessfulStatus,good,ite_true] using status,by simpa only [good,ite_true] using frame,
        plaintext hCall long small fr (mem ▸ data good)⟩

end ChaCha20Poly1305.Statements
