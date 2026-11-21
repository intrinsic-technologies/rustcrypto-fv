import ChaCha20Poly1305.Proofs.Encrypt.Prefix
import ChaCha20Poly1305.Proofs.Encrypt.Suffix
import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Statements

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86

theorem chacha20poly1305_encrypt_writes_ciphertext_with_tag
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall encrypt initial [key, nonce, associatedData, plaintext]) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion encrypt initial,
          heapRegion encrypt initial, allocatorStateRegion,
          Stack.region initial encrypt.minStackBytes] ∧
      readOutput encrypt initial final =
        .ok (AEAD.encryptWithTag associatedData key nonce plaintext) := by
  have entry := ChaCha20Poly1305.Proofs.Wrapper.entry_ready bindings hBindings hMachine hCall.programLoaded
  have hb := X86Proofs.nearReturn64Boundary_eq initial entry.ready.dataReady hMachine.integer.ss
    (ChaCha20Poly1305.Proofs.Wrapper.stack_return_readable hCall.stackAvailable)
  obtain ⟨address, hSlot, _, outside⟩ := hCall.returnAddress
  have hr := ChaCha20Poly1305.Proofs.Wrapper.word64At_memLoad hSlot
  have hrip : (X86Proofs.returnBoundary initial).rip = address := by
    simp only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hr
    exact hr
  have hout : ¬ InProgram (X86Proofs.returnBoundary initial).rip := by
    simpa only [hrip] using outside
  obtain ⟨m, s, adv, pre, atCore⟩ :=
    ChaCha20Poly1305.Proofs.Encrypt.entry_to_core hBindings hMachine hCall
  have hin : InProgram (0x101866 : BitVec 64) := ⟨0x80, by decide +kernel⟩
  have hdiff : (X86Proofs.returnBoundary initial).rip ≠ (X86Proofs.returnBoundary s).rip := by
    rw [atCore.returnAddress]
    intro h
    exact hout (h ▸ hin)
  have hlow : (X86Proofs.returnBoundary s).rip.toNat < 2 ^ 32 := by
    rw [atCore.returnAddress]
    decide
  obtain ⟨n, t, core, post⟩ := ChaCha20Poly1305.Proofs.Core.core_call
    (X86Proofs.returnBoundary initial) pre hout hdiff hlow
  obtain ⟨k, final, ret, hm, he, hs, hd, hf, ho⟩ :=
    ChaCha20Poly1305.Proofs.Encrypt.core_return hCall atCore hout post
  obtain ⟨least, unique⟩ := X86Proofs.Returns.unique_of_boundary hb ((adv.trans core).returns ret)
  exact ⟨least, final, unique, hm, he, hs, hd, hf, ho⟩

end ChaCha20Poly1305.Statements
