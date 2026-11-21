import K256.Proofs.Verify.Wrapper.Frame

namespace K256.Proofs.Verify.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

theorem inputMemory {s : RamState} {key message sig : ByteArray} {m : Ram}
    (call : ValidCall verifyingKeyVerify s [key,message,sig])
    (frame : RamWriteFrame s.external m [stack s]) :
    (registerRegion s .rdi 65).HasBytes m key ∧
    (registerRegion s .rsi message.size).HasBytes m message ∧
    (registerRegion s .rcx 64).HasBytes m sig ∧
    ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2 := by
  have sep : MemorySeparation [stack s] [registerRegion s .rdi 65,
      registerRegion s .rsi message.size, registerRegion s .rcx 64] := call.separation
  obtain ⟨avoid, apart⟩ := sep.2 (stack s) List.mem_cons_self
  have writes : MemoryWriteFrame s {s with external := m} #v[stack s] :=
    frame.memoryWriteFrame fun _ none _ hr => none _ (Vector.mem_toList_iff.mp hr)
  have bytes {r : MemoryRegion} {bs : ByteArray} (valid : ValidInput s r bs)
      (member : r ∈ [registerRegion s .rdi 65,registerRegion s .rsi message.size,
        registerRegion s .rcx 64]) : r.HasBytes m bs :=
    Common.hasBytes_of_memoryWriteFrame writes valid.2.2 valid.2.1 (by
      intro reg h a ha
      obtain rfl := Vector.mem_singleton.mp h
      exact fun hs => apart r member a hs ha)
  obtain ⟨keyMem, msgMem, sigMem, _⟩ := call.inputsInMemory
  refine ⟨bytes keyMem (by simp), bytes msgMem (by simp), bytes sigMem (by simp), ?_⟩
  have loaded := Common.programLoaded_of_memoryWriteFrame writes call.programLoaded (by
    intro reg h
    obtain rfl := Vector.mem_singleton.mp h
    exact fun addr inside there => avoid addr inside (Or.inl there))
  exact fun b hb => loaded b.1 b.2 (Common.programSections_fetchByte_of_mem hb)

theorem decodedInputs {s : RamState} {key message sig : ByteArray}
    (call : ValidCall verifyingKeyVerify s [key,message,sig]) :
    ∃ p r t, Secp256k1.decodePublicKey key = some p ∧ Ecdsa.signatureScalars sig = some (r,t) := by
  have hk : (Secp256k1.decodePublicKey key).isSome := call.inputsHoldValues.1
  have hs : (Ecdsa.signatureScalars sig).isSome := call.inputsHoldValues.2.2.1
  obtain ⟨p,hp⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨⟨r,t⟩,hr⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨p,r,t,hp,hr⟩

end K256.Proofs.Verify.Wrapper
