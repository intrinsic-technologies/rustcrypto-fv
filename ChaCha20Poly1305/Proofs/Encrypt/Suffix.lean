import ChaCha20Poly1305.Proofs.Encrypt.Contract
import ChaCha20Poly1305.Proofs.Encrypt.Append
import ChaCha20Poly1305.Proofs.Encrypt.Suffix.Bridge
import ChaCha20Poly1305.Proofs.Encrypt.Suffix.Supply
import ChaCha20Poly1305.Proofs.Encrypt.Suffix.Output

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract

set_option maxRecDepth 8000 in
theorem core_return [bindings : Bindings] {initial s t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, associatedData, plaintext])
    (atCore : AtCore initial s plaintext.size)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (post : CorePost s t key nonce associatedData plaintext (initial.regValue .r8)) :
    ∃ fuel final, Returns (returnBoundary initial) fuel t final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
          Stack.region initial encrypt.minStackBytes] ∧
      readOutput encrypt initial final = .ok (AEAD.encryptWithTag associatedData key nonce plaintext) := by
  have st := Suffix.entry_stack hc
  have growsT : Wrapper.Grows initial t := fun a ha => post.grows a (atCore.grows a ha)
  have readyT : ReadyToStep t := ReadyToStep.of_supported post.machine
    post.environment.smrr post.environment.memoryType
    (DecoderFeatures.of_supported post.machine post.environment.leadingZeroCount)
  have rspT : stackPtr t = stackPtr initial - 168 := by
    as_aux_lemma =>
      rw [post.rsp, atCore.rsp]; bv_omega
  obtain ⟨n1, u, au, Tu, ripU, rspU, diU, siU, dxU, retU, tag0, tag8⟩ :=
    Suffix.to_append st growsT outside ⟨readyT, post.code, AgreesExcept.refl _ _⟩
      (post.rip.trans atCore.returnAddress) rspT
      (by rw [Suffix.core_result_zero hc atCore post]; rfl)
  have preU := Suffix.append_pre hc atCore post Tu ripU rspU diU siU dxU tag0 tag8
  have boundaryU : (returnBoundary u).rip = 0x101893 := by
    as_aux_lemma =>
      change Wrapper.wd u (stackPtr u) = _
      rw [rspU]; exact retU
  obtain ⟨n2, v, av, pv⟩ := append_call (returnBoundary initial) preU outside
    (by rw [boundaryU]; exact (Wrapper.code_ne_boundary outside 0x1893 (by omega)).symm)
    (by rw [boundaryU]; decide)
  have growsU : Wrapper.Grows initial u := growsT.step Tu.agrees
  have growsV : Wrapper.Grows initial v := fun a ha => pv.grows a (growsU a ha)
  have rspV : stackPtr v = stackPtr initial - 168 := by
    as_aux_lemma =>
      rw [pv.rsp, rspU]; bv_omega
  have ripV : v.RIP = 0x101893 := pv.rip.trans boundaryU
  have frameTU := Suffix.setup_frame st Tu
  have frameUV := Suffix.append_frame hc rspU diU pv
  let regions := #v[outputRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
    Stack.region initial encrypt.minStackBytes]
  have frameU : MemoryWriteFrame initial u regions := memoryWriteFrame_trans
    (Suffix.core_frame hc atCore post) (Wrapper.frame_widen frameTU (by
      intro r hr a ha
      have e : r = Stack.region initial encrypt.minStackBytes := by simpa using hr
      subst r
      exact ⟨_, by simp [regions], ha⟩))
  have frameV : MemoryWriteFrame initial v regions := memoryWriteFrame_trans frameU
    (Wrapper.frame_widen frameUV (by
      intro r hr a ha
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp [regions], ha⟩))
  have heap := (hc.heapInMemory rfl).1
  rw [heap_region hc] at heap
  have heapBound : (initial.regValue .r8).toNat + (plaintext.size + 16) < userAddressLimit := heap.1
  have sizeBound : plaintext.size + 16 < 2^64 := by unfold userAddressLimit at heapBound; omega
  have lengthNat : (BitVec.ofNat 64 (plaintext.size + 16)).toNat = plaintext.size + 16 :=
    Nat.mod_eq_of_lt sizeBound
  have pair := hc.separation.1
  have wr : writtenRegions encrypt initial [key, nonce, associatedData, plaintext] =
      [bufferRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial 1168] := rfl
  rw [wr] at pair
  have heapStack := (List.pairwise_cons.mp pair.tail).1 (Stack.region initial 1168) (by simp)
  rw [heap_region hc] at heapStack
  have ctBound : (messageRegion (initial.regValue .r8) plaintext.size).Bounded := by
    as_aux_lemma =>
      change (initial.regValue .r8).toNat + plaintext.size < userAddressLimit
      omega
  have ctU := Suffix.hasBytes_frame frameTU ctBound (by
    intro r hr a ha hm
    have e : r = Stack.region initial encrypt.minStackBytes := by simpa using hr
    subst r
    apply heapStack a ?_ ha
    simp only [messageRegion, registerRegion, MemoryRegion.Contains] at hm ⊢
    omega) post.ciphertext
  have bytesV := Suffix.append_bytes hc rspU diU ctU pv
  have retV : Wrapper.wd v (stackPtr initial) = (returnBoundary initial).rip := by
    as_aux_lemma =>
      have h1 := Suffix.append_post_word_kept hc rspU diU pv (k := 0) (by omega) (by omega)
      have h2 := Suffix.append_word_kept Tu (k := 0) (by omega) (by omega)
      have h3 := Suffix.core_return_word hc atCore post
      simp only [BitVec.sub_zero] at h1 h2
      exact h1.trans (h2.trans h3)
  have keepWord (k : Nat) (hk : k ≤ 168) (apart : 160 ≤ k)
      {val : BitVec 64} (word : (localWord initial k).Word64At s.external val) :
      Wrapper.wd v (stackPtr initial - BitVec.ofNat 64 k) = val := by
    as_aux_lemma =>
      rw [Suffix.append_post_word_kept hc rspU diU pv hk (by omega),
        Suffix.append_word_kept Tu hk (by omega), Suffix.core_word_kept hc atCore post hk (by omega)]
      have h := Wrapper.word64At_memLoad word
      have addr : BitVec.ofNat 64 (localWord initial k).start = stackPtr initial - BitVec.ofNat 64 k := by
        apply BitVec.eq_of_toNat_eq
        change ((stackPtr initial).toNat - k) % 2^64 = _
        rw [Wrapper.slot_toNat0 (by have := st.room; omega)]
        have := st.top; omega
      rw [addr] at h
      exact h
  have capV := keepWord 168 (by omega) (by omega) atCore.capacity
  have ptrV := keepWord 160 (by omega) (by omega) atCore.pointer
  have lenV : Wrapper.wd v (stackPtr initial - 152) = BitVec.ofNat 64 (plaintext.size + 16) := by
    as_aux_lemma =>
      have h := Wrapper.word64At_memLoad pv.lengthWord
      have diNat : (u.regValue .rdi).toNat = (stackPtr initial).toNat - 168 := by
        change (Wrapper.rd u 7).toNat = _
        rw [diU]; exact Wrapper.slot_toNat0 (k := 168) (by have := st.room; omega)
      have addr : BitVec.ofNat 64 ((u.regValue .rdi).toNat + 16) = stackPtr initial - 152 := by
        rw [diNat]
        apply BitVec.eq_of_toNat_eq
        change ((stackPtr initial).toNat - 168 + 16) % 2^64 =
          (stackPtr initial - BitVec.ofNat 64 152).toNat
        rw [Wrapper.slot_toNat0 (k := 152) (by have := st.room; omega)]
        have := st.room; have := st.top; omega
      rw [addr] at h
      exact h
  have readyV := ReadyToStep.of_supported pv.machine pv.environment.smrr pv.environment.memoryType
    (DecoderFeatures.of_supported pv.machine pv.environment.leadingZeroCount)
  have outV : Wrapper.rd v 3 = initial.regValue .r9 :=
    (pv.calleeSaved .rbx (by simp)).trans ((Tu.agrees.read (r := 3) (n := 64) (by simp [Suffix.appendCs])).trans
      ((post.calleeSaved .rbx (by simp)).trans atCore.rbx))
  obtain ⟨cap, capRead, capRoom, capLow⟩ := Suffix.output_capacity hc frameV
  have notMax : Wrapper.wd v (stackPtr initial - 168) ≠ -1 := by
    as_aux_lemma =>
      change Wrapper.wd v (stackPtr initial - BitVec.ofNat 64 168) ≠ -1
      rw [capV]
      intro eq
      have he := congrArg BitVec.toNat eq
      change (BitVec.ofNat 64 (plaintext.size + 16)).toNat = 18446744073709551615 at he
      rw [lengthNat] at he
      unfold userAddressLimit at heapBound
      omega
  have reads : ∀ d ∈ [0, 8, 16, 200],
      MemReadable v (stackPtr initial - 168 + BitVec.ofNat 64 d) 8 := by
    as_aux_lemma =>
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · have e : stackPtr initial - 168 + BitVec.ofNat 64 0 = stackPtr initial - BitVec.ofNat 64 168 := by bv_omega
        rw [e]
        exact Suffix.stack_readable st growsV (k := 168) (n := 8) (by omega) (by omega)
      · have e : stackPtr initial - 168 + BitVec.ofNat 64 8 = stackPtr initial - BitVec.ofNat 64 160 := by bv_omega
        rw [e]; exact Suffix.stack_readable st growsV (by omega) (by omega)
      · have e : stackPtr initial - 168 + BitVec.ofNat 64 16 = stackPtr initial - BitVec.ofNat 64 152 := by bv_omega
        rw [e]; exact Suffix.stack_readable st growsV (by omega) (by omega)
      · have e : stackPtr initial - 168 + BitVec.ofNat 64 200 = stackPtr initial + BitVec.ofNat 64 32 := by bv_omega
        rw [e]
        obtain ⟨cap0, arg, _⟩ := hc.outputLengthArgumentCoversOutput rfl (.stack 3) rfl
        have rd := Wrapper.loadBytes_isSome arg.2.2
        have addr : BitVec.ofNat 64 (stackArgumentSlot initial 3).start = stackPtr initial + BitVec.ofNat 64 32 := by
          change BitVec.ofNat 64 ((stackPtr initial).toNat + 32) = _
          rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rw [addr] at rd
        refine ⟨?_, fun i hi => growsV _ (rd i hi)⟩
        rw [toNat_add_ofNat _ _ (by unfold userAddressLimit at capLow; omega)]
        unfold userAddressLimit at capLow; omega
  obtain ⟨w, aw, readyW, codeW, agreeW, ripW, rspW, retW, diW, siW, dxW⟩ :=
    output_enter_memcpy st outside readyV pv.code growsV ripV rspV pv.success outV reads notMax
      lenV ptrV capRead (by rw [lengthNat]; exact capRoom)
  have growsW : Wrapper.Grows initial w := growsV.step agreeW
  have machineW : SupportedIntegerMachineState bindings.processor w :=
    ⟨readyW.cpu, SupportedSSE.of_agreesExcept agreeW pv.machine.sse, readyW.memory, readyW.ready⟩
  have envW : MachineRamUnitStrideDecodable bindings w :=
    ⟨readyW.smrr, readyW.memoryType, pv.environment.stringStride, readyW.features.lzcnt⟩
  have dfW : DirectionFlagUnset w := agreeW.directionFlagClear
    (by simp [outputEntryChanges, outputPrepChanges]) pv.directionFlagUnset
  have preW := Suffix.memcpy_pre hc growsW dfW ripW rspW diW siW dxW retW
  have frameVW := output_entry_frame st agreeW
  have frameW : MemoryWriteFrame initial w regions := memoryWriteFrame_trans frameV
    (Wrapper.frame_widen frameVW (by
      intro r hr a ha
      have e : r = Stack.region initial encrypt.minStackBytes := by simpa using hr
      subst r
      exact ⟨_, by simp [regions], ha⟩))
  have heapW := Suffix.hasBytes_frame frameVW (by rw [heap_region hc]; exact heap.1) (by
    intro r hr a ha hm
    have e : r = Stack.region initial encrypt.minStackBytes := by simpa using hr
    subst r
    apply heapStack a ?_ ha
    rwa [heap_region hc] at hm) bytesV
  have destination : MemoryContracts.destination w = outputRegion encrypt initial := by
    as_aux_lemma =>
      rw [output_region hc]
      change (⟨(Wrapper.rd w 7).toNat, (Wrapper.rd w 2).toNat⟩ : MemoryRegion) = _
      rw [diW, dxW, lengthNat]
      rfl
  have sourceW : (⟨(X86Proofs.rsi.read w).toNat,
      (MemoryContracts.rdx.read w).toNat⟩ : MemoryRegion).HasBytes w.external
      (AEAD.encryptWithTag associatedData key nonce plaintext) := by
    as_aux_lemma =>
      change (⟨(Wrapper.rd w 6).toNat, (Wrapper.rd w 2).toNat⟩ : MemoryRegion).HasBytes _ _
      rw [siW, dxW, lengthNat]
      rw [heap_region hc] at heapW
      exact heapW
  have present : Wrapper.RetPresent (stackPtr initial) w := by
    as_aux_lemma =>
      intro i hi
      apply growsW
      apply st.allocated <;> rw [Wrapper.slot_toNat (k := 104) (by have := st.room; omega) st.top (by omega)] <;>
        have := st.room <;> omega
  have retFinal : Wrapper.wd w (stackPtr initial) = (returnBoundary initial).rip := by
    as_aux_lemma =>
      have h := output_entry_word_kept st agreeW (k := 0) (by omega)
      simp only [BitVec.sub_zero] at h
      exact h.trans retV
  have saves {k : Nat} (hk : k ≤ 48) {val : BitVec 64}
      (word : (localWord initial k).Word64At s.external val) :
      Wrapper.wd w (stackPtr initial - BitVec.ofNat 64 k) = val :=
    (output_entry_word_kept st agreeW (by omega)).trans
      (Suffix.saved_word hc atCore post Tu rspU diU pv hk word)
  have apart : (MemoryContracts.destination w).Disjoint (Stack.region initial 48) := by
    as_aux_lemma =>
      rw [destination, output_region hc]
      have outputStack := (List.pairwise_cons.mp pair).1 (Stack.region initial 1168) (by simp)
      have buf : bufferRegion encrypt initial = registerRegion initial .r9 (plaintext.size + 16) := by
        change registerRegion initial .r9 (messageBytes encrypt initial + 16) = _
        rw [message_length hc]
      rw [buf] at outputStack
      intro a ha hs
      apply outputStack a ha
      have room : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
      rw [Wrapper.stack_region_eq initial 1168 room]
      rw [Wrapper.stack_region_eq initial 48 (by omega)] at hs
      simp only [MemoryRegion.Contains] at hs ⊢
      omega
  have low : (returnBoundary initial).rip.toNat < 2^32 := by
    as_aux_lemma =>
      obtain ⟨addr, slot, low, _⟩ := hc.returnAddress
      have h := Wrapper.word64At_memLoad slot
      have eq : (returnBoundary initial).rip = addr := by
        simp only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
        exact h
      rw [eq]; exact low
  have boundary := Suffix.outside_memcpy outside
  obtain ⟨n3, fin, copied, af, mf, ef, cf, df, ff, copy, mem, _⟩ :=
    output_copy_return st outside low boundary readyW codeW machineW envW dfW preW rspW retW
      present apart retFinal (saves (k := 48) (by omega) atCore.savedRbx) (saves (k := 40) (by omega) atCore.savedR12)
      (saves (k := 32) (by omega) atCore.savedR13) (saves (k := 24) (by omega) atCore.savedR14)
      (saves (k := 16) (by omega) atCore.savedR15) (saves (k := 8) (by omega) atCore.savedRbp)
  refine ⟨_, fin, au.returns (av.returns (aw.returns af)), mf, ef, cf, df, ?_, ?_⟩
  · apply memoryWriteFrame_trans frameW
    apply Wrapper.frame_widen ff
    intro r hr a ha
    have e : r = MemoryContracts.destination w := by simpa using hr
    subst r
    rw [destination] at ha
    exact ⟨_, by simp [regions], ha⟩
  · apply Wrapper.readRegion_of_hasBytes
    have hb := Suffix.memcpy_hasBytes copy sourceW
    rw [destination] at hb
    change (outputRegion encrypt initial).HasBytes fin.external _
    rw [mem]
    exact hb

end ChaCha20Poly1305.Proofs.Encrypt
