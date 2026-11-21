import ChaCha20Poly1305.Proofs.Decrypt.Empty
import ChaCha20Poly1305.Proofs.Decrypt.Call
import ChaCha20Poly1305.Proofs.Decrypt.Lifted

namespace ChaCha20Poly1305.Proofs.Decrypt

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine Prelude
open ChaCha20Poly1305.Spec.Program

theorem emptyInput [b : Bindings] {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hb : MachineRamUnitStrideDecodable b s)
    (hm : SupportedIntegerMachineState b.processor s) (hc : ValidCall decrypt s [key, nonce, aad, msg])
    (hz : msg.size = 0) :
    ∃ fuel t, UniqueExecution s fuel t ∧ SupportedIntegerMachineState b.processor t ∧
      MachineRamUnitStrideDecodable b t ∧ CalleeSavedRegistersUnchanged s t ∧ DirectionFlagUnset t ∧
      FailureStatus t aeadErrorStatus ∧ MemoryWriteFrame s t
        #v[heapRegion decrypt s, allocatorStateRegion, Stack.region s decrypt.minStackBytes] := by
  obtain ⟨ret, hret, hl, ho⟩ := hc.returnAddress
  let fr := Activation.ofEntry s decrypt.minStackBytes ret
  let rsp := s.regValue .rsp
  have hf := callPre hc hret hl ho
  have hslot : StackArgument s 1 (BitVec.ofNat 64 msg.size) :=
    hc.lengthArgumentsMatchInputs.2.2.2.1
  obtain ⟨cap, hcap, _⟩ := hc.heapLengthArgumentCoversHeap _ rfl
  have slotRead : Readable s.external (rsp + 16) 16 := by
    have hlow : rsp.toNat + 8 * (2 + 1) + 8 < 2^32 := hcap.1
    have h := Readable.of_word64At (mem := s.external) (start := rsp.toNat + 16)
      (n := 2) (vals := fun i => if i = 0 then BitVec.ofNat 64 msg.size else cap) (by
        intro i hi
        rcases i with _ | i
        · simpa [stackArgumentSlot, rsp] using hslot.2
        · have ei : i = 0 := by omega
          subst i
          simpa [stackArgumentSlot, rsp, Nat.add_assoc] using hcap.2) (by omega)
    simpa [BitVec.ofNat_add] using h
  have slotZero : memLoad s.external (rsp + 16) 64 = 0 := by
    have h := memLoad_of_word64At hslot.2
    simpa [hz, stackArgumentSlot, rsp, BitVec.ofNat_add] using h
  have keyBytes : ValidInput s (registerRegion s .rdi 32) (key : ByteArray) := hc.inputsInMemory.1
  have keyRead : Readable s.external (s.regValue .rdi) 32 := by
    have h := Readable.of_hasBytes keyBytes.2 keyBytes.1
    rw [show (key : ByteArray).size = 32 from key.size_toArray] at h
    simpa [registerRegion] using h
  obtain ⟨ks, ka, sa, aa⟩ := call_apart hc
  let rs := #v[heapRegion decrypt s, allocatorStateRegion, Stack.region s decrypt.minStackBytes]
  have hr := Lifted.Decrypt.routine Empty.core (regions := rs)
    (Lifted.blocks hb.stringStride Lifted.fnCode fun _ h => h) Empty.blocks
    (callEntry hb hm hc) hf (c := ()) (lab := Empty.Label.entry) (p := ()) (by
      apply outside_of_within (regions := rs) (small := [fr.region, allocatorStateRegion])
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨Stack.region s decrypt.minStackBytes, by simp [rs], Activation.ofEntry_region_within⟩,
        ⟨allocatorStateRegion, by simp [rs], fun _ h => h⟩⟩)
    (.done (output := ⟨#v[], none, ()⟩) rfl) (by
      exact ⟨keyRead, slotRead, slotZero, allocator_writable hc, stack_text_apart hc, ks, ka, sa, aa, trivial⟩)
  obtain ⟨fuel, t, hu, hm', hframe, hdf, habi, _, _, _, lo, hrel, hat⟩ := hr
  refine ⟨fuel, t, hu, hm', ⟨hrel.ready.smrr, hrel.ready.memoryType, hb.stringStride,
      hrel.ready.features.lzcnt⟩, sysVCalleeReturn_calleeSaved habi, hdf, ?_, hframe⟩
  have hv := hrel.regs 0 (by decide) (by decide +kernel)
  have hr0 : lo.values[0] = ⟨64, 1⟩ := hat.1
  have he : t.regValue .rax = 1 := Value.eq_bits (hv.symm.trans hr0)
  simp [FailureStatus, he, aeadErrorStatus]

end ChaCha20Poly1305.Proofs.Decrypt
