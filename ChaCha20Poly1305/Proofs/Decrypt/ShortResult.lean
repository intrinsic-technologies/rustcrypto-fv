import ChaCha20Poly1305.Proofs.Decrypt.Short
import ChaCha20Poly1305.Proofs.Decrypt.Lifted

namespace ChaCha20Poly1305.Proofs.Decrypt

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine Prelude
open ChaCha20Poly1305.Spec.Program

theorem shortInput [b : Bindings] {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {aad msg : ByteArray} (hb : MachineRamUnitStrideDecodable b s)
    (hm : SupportedIntegerMachineState b.processor s) (hc : ValidCall decrypt s [key, nonce, aad, msg])
    (hp : 0 < msg.size) (hl : msg.size < 16) :
    ∃ fuel t, UniqueExecution s fuel t ∧ SupportedIntegerMachineState b.processor t ∧
      MachineRamUnitStrideDecodable b t ∧ CalleeSavedRegistersUnchanged s t ∧ DirectionFlagUnset t ∧
      FailureStatus t aeadErrorStatus ∧ MemoryWriteFrame s t
        #v[heapRegion decrypt s, allocatorStateRegion, Stack.region s decrypt.minStackBytes] := by
  obtain ⟨ret, hret, hrl, ho⟩ := hc.returnAddress
  obtain ⟨cap, hcap, hcapLen⟩ := hc.heapLengthArgumentCoversHeap _ rfl
  let e := Short.envOf s msg cap
  have hg : Short.Geometry e := Short.call_geometry hc hcapLen hp hl
  let fr := Activation.ofEntry s decrypt.minStackBytes ret
  let c := {fr with rbp := 1, r12 := fr.r8 + e.n, r13 := Short.limit e}
  have hf := callPre hc hret hrl ho
  let rsp := s.regValue .rsp
  have hslot : StackArgument s 1 e.n := hc.lengthArgumentsMatchInputs.2.2.2.1
  have slotRead : Readable s.external (rsp + 16) 16 := by
    have hlow : rsp.toNat + 8 * (2 + 1) + 8 < 2^32 := hcap.1
    have h := Readable.of_word64At (mem := s.external) (start := rsp.toNat + 16)
      (n := 2) (vals := fun i => if i = 0 then e.n else cap) (by
        intro i hi
        rcases i with _ | i
        · simpa [stackArgumentSlot, rsp] using hslot.2
        · have ei : i = 0 := by omega
          subst i
          simpa [stackArgumentSlot, rsp, Nat.add_assoc] using hcap.2) (by omega)
    simpa [BitVec.ofNat_add] using h
  have sLen : memLoad s.external (rsp + 16) 64 = e.n := by
    simpa [stackArgumentSlot, rsp, BitVec.ofNat_add] using memLoad_of_word64At hslot.2
  have sCap : memLoad s.external (rsp + 24) 64 = cap := by
    simpa [stackArgumentSlot, rsp, BitVec.ofNat_add] using memLoad_of_word64At hcap.2
  have keyBytes : ValidInput s (registerRegion s .rdi 32) (key : ByteArray) := hc.inputsInMemory.1
  have keyRead : Readable s.external (s.regValue .rdi) 32 := by
    have h := Readable.of_hasBytes keyBytes.2 keyBytes.1
    rw [show (key : ByteArray).size = 32 from key.size_toArray] at h
    simpa [registerRegion] using h
  have hnat : e.n.toNat = msg.size := Nat.mod_eq_of_lt (by omega)
  have hsIn : ValidInput s (registerRegion s .rcx msg.size) msg := hc.inputsInMemory.2.2.2.1
  have srcRead : Readable s.external fr.rcx e.n.toNat := by
    rw [hnat]
    simpa [fr, Activation.ofEntry, registerRegion] using Readable.of_hasBytes hsIn.2 hsIn.1
  have heapWrite : Writable Lifted.fnCode s.external fr.r8 e.n.toNat := by
    rw [hnat]
    have he := Short.heap_region hc
    have hheap := (hc.heapInMemory rfl).1
    rw [he] at hheap
    apply Writable.of_avoids (region := registerRegion s .r8 msg.size) (forbidden := Forbidden)
      hheap.1 hheap.2 _ code_forbidden tables_forbidden (Nat.le_refl _) (Nat.le_refl _) hp
    rw [← he]
    apply hc.separation.2.2
    simp [writtenRegions, decrypt]
  obtain ⟨ks, ka, _, _⟩ := call_apart hc
  let rs := #v[heapRegion decrypt s, allocatorStateRegion, Stack.region s decrypt.minStackBytes]
  have hr := Lifted.Decrypt.routine (Short.core e) (regions := rs)
    (Lifted.blocks hb.stringStride Lifted.fnCode fun _ h => h) (Short.blocks e hg)
    (callEntry hb hm hc) hf (c := c) (lab := Short.Label.entry) (p := ()) (by
      apply outside_of_within (regions := rs) (small := [fr.region, ⟨e.heap.toNat,e.n.toNat⟩, allocatorStateRegion])
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨⟨Stack.region s decrypt.minStackBytes, by simp [rs], Activation.ofEntry_region_within⟩,
        ⟨heapRegion decrypt s, by simp [rs], ?_⟩, ⟨allocatorStateRegion, by simp [rs], fun _ h => h⟩⟩
      rw [Short.heap_region hc, hnat]; exact fun _ h => h)
    Short.executes (by
      exact ⟨rfl, rfl, rfl, Activation.ofEntry_low_toNat, rfl, rfl, rfl, srcRead,
        heapWrite, allocator_writable hc, keyRead, slotRead, sLen, sCap, ks, ka, trivial⟩)
  obtain ⟨fuel, t, hu, hm', hframe, hdf, habi, _, _, _, lo, hrel, hat⟩ := hr
  refine ⟨fuel, t, hu, hm', ⟨hrel.ready.smrr, hrel.ready.memoryType, hb.stringStride,
      hrel.ready.features.lzcnt⟩, sysVCalleeReturn_calleeSaved habi, hdf, ?_, hframe⟩
  have hv := hrel.regs 0 (by decide) (by decide +kernel)
  have hr0 : lo.values[0] = ⟨64, 1⟩ := hat.1
  have he : t.regValue .rax = 1 := Value.eq_bits (hv.symm.trans hr0)
  simp [FailureStatus, he, aeadErrorStatus]

end ChaCha20Poly1305.Proofs.Decrypt
