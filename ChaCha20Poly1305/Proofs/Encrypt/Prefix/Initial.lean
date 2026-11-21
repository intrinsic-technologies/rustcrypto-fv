import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Initial.Prologue
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Initial.Entry
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Initial.Length
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Initial.Finish

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract Wrapper MemoryRoutines.Machine

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem initial_to_alloc [bindings : Bindings] {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hc : ValidCall encrypt initial [key, nonce, associatedData, plaintext]) :
    ∃ fuel s, Advances (returnBoundary initial) fuel initial s ∧
      BeforeAlloc initial s key plaintext.size := by
  have hs := initial_stack hc
  have hroom := hs.room
  have htop := hs.top
  have ready := Wrapper.entry_ready bindings hb hm hc.programLoaded
  have outside : ¬ InProgram (returnBoundary initial).rip := by
    obtain ⟨address, slot, _, hout⟩ := hc.returnAddress
    have hr := word64At_memLoad slot
    have he : (returnBoundary initial).rip = address := by
      simp only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hr
      exact hr
    exact he ▸ hout
  obtain ⟨u, au, U, ripU, spU, regsU, w8, w16, w24, w32, w40, w48⟩ :=
    save_registers hs outside ⟨ready.ready, ready.code, AgreesExcept.refl _ _⟩ hc.atEntryPoint
  have len : StackArgument initial 1 (BitVec.ofNat 64 plaintext.size) :=
    hc.lengthArgumentsMatchInputs.2.2.2.1
  obtain ⟨cap, capSlot, _⟩ := hc.heapLengthArgumentCoversHeap _ (by rfl)
  change StackArgument initial 2 cap at capSlot
  have loadCap : MemReadable u (stackPtr u + 192) 8 := by
    have h := argument_readable capSlot
    have he : stackPtr u + 192 = stackPtr initial + BitVec.ofNat 64 (8*(2+1)) := by
      rw [spU]; bv_omega
    rw [he]
    exact ⟨h.low, fun i hi => U.grows _ (h.mem i hi)⟩
  have loadLen : MemReadable u (stackPtr u + 184) 8 := by
    have h := argument_readable len
    have he : stackPtr u + 184 = stackPtr initial + BitVec.ofNat 64 (8*(1+1)) := by
      rw [spU]; bv_omega
    rw [he]
    exact ⟨h.low, fun i hi => U.grows _ (h.mem i hi)⟩
  have allocMem : MemWritable u 0x300000 16 := by
    refine ⟨by decide, ?_, by decide⟩
    intro i hi
    apply U.grows
    obtain ⟨b, hb⟩ := (hc.heapInMemory rfl).2 (0x300000 + BitVec.ofNat 64 i) (by
      change 0x300000 ≤ _ ∧ _ < 0x300000 + 16
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
        show (0x300000 : BitVec 64).toNat = 0x300000 from rfl]
      omega)
    simp only [hb, Option.isSome_some]
  have allocAvoid : ∀ a, (Component.mem 0x300000 16).Covers a → ¬ InProgram a := by
    rintro a ⟨i, hi, rfl⟩ hp
    apply hc.separation.2.2 allocatorStateRegion (by simp [writtenRegions, encrypt]) _ _ (Or.inl hp)
    change 0x300000 ≤ _ ∧ _ < 0x300000 + 16
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
        show (0x300000 : BitVec 64).toNat = 0x300000 from rfl]
    omega
  have allocSep : ∀ i < 16, ¬ (Component.mem 0x300000 16).Covers
      (stackPtr u + 184 + BitVec.ofNat 64 i) := by
    have d1 := region_sep (hc.separation.2.1 allocatorStateRegion
      (by simp [writtenRegions, encrypt]) (stackArgumentSlot initial 1)
      (by simp [readRegions, encrypt, argumentRegions])) (by decide) (by change 0 < 8; decide)
    have d2 := region_sep (hc.separation.2.1 allocatorStateRegion
      (by simp [writtenRegions, encrypt]) (stackArgumentSlot initial 2)
      (by simp [readRegions, encrypt, argumentRegions])) (by decide) (by change 0 < 8; decide)
    simp only [allocatorStateRegion, stackArgumentSlot] at d1 d2
    rintro i hi ⟨j, hj, he⟩
    rw [spU] at he
    have hx := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
      show (168 : BitVec 64).toNat = 168 from rfl,
      show (184 : BitVec 64).toNat = 184 from rfl,
      show (0x300000 : BitVec 64).toNat = 0x300000 from rfl] at hx
    change 0x300000 + 16 ≤ (stackPtr initial).toNat + 8*(1+1) ∨
      (stackPtr initial).toNat + 8*(1+1) + 8 ≤ 0x300000 at d1
    change 0x300000 + 16 ≤ (stackPtr initial).toNat + 8*(2+1) ∨
      (stackPtr initial).toNat + 8*(2+1) + 8 ≤ 0x300000 at d2
    omega
  obtain ⟨v, av, V, ripV, r12V, r13V, headV, limitV⟩ := initialize_allocator
    outside ⟨U.ready, U.code, AgreesExcept.refl _ _⟩ ripU loadCap loadLen allocMem allocAvoid allocSep
  have spV : stackPtr v = stackPtr initial - 168 :=
    sp_keep V.agrees (by simp [allocatorChanges]) spU
  have growsV : Grows initial v := U.grows.step V.agrees
  have rdiV : rd v 7 = initial.regValue .rdi :=
    (V.agrees.read (by simp [allocatorChanges])).trans (regsU 7 (by decide))
  have key0 : ValidInput initial (registerRegion initial .rdi 32) ⟨key.toArray⟩ := hc.inputsInMemory.1
  have kb : (initial.regValue .rdi).toNat + 32 < 2^32 := key0.1
  have ks := region_sep (hc.separation.2.1 (Stack.region initial 1168)
    (by simp [writtenRegions, encrypt]) (registerRegion initial .rdi 32)
    (by simp [readRegions, encrypt, inputRegion])) (by
      change 0 < (stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168); omega)
    (by change 0 < 32; decide)
  change (stackPtr initial).toNat - 1168 + ((stackPtr initial).toNat + 8 -
      ((stackPtr initial).toNat - 1168)) ≤ (initial.regValue .rdi).toNat ∨
      (initial.regValue .rdi).toNat + 32 ≤ (stackPtr initial).toNat - 1168 at ks
  have keyU := Wrapper.input_kept hs (U.frame hs) (by
    apply disjoint_of_sep
    change (stackPtr initial).toNat - 1104 + 1112 ≤ (initial.regValue .rdi).toNat ∨
      (initial.regValue .rdi).toNat + 32 ≤ (stackPtr initial).toNat - 1104
    omega) key0
  have keyAlloc := hc.separation.2.1 allocatorStateRegion
    (by simp [writtenRegions, encrypt]) (registerRegion initial .rdi 32)
    (by simp [readRegions, encrypt, inputRegion])
  have keyV : ValidInput v (registerRegion initial .rdi 32) ⟨key.toArray⟩ := by
    apply input_preserved keyU
    intro a ha
    apply V.agrees.byte
    intro c hc'
    simp only [allocatorChanges, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact nonmem_not_covers rfl _
      | (rintro ⟨i, hi, he⟩; apply keyAlloc a.toNat _ ha; rw [he]
         change 0x300000 ≤ _ ∧ _ < 0x300000 + 16
         simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
           show (0x300000 : BitVec 64).toNat = 0x300000 from rfl]
         omega)
  have kr : ∀ j < 32, (v.external[rd v 7 + BitVec.ofNat 64 j]?).isSome := by
    intro j hj
    have hb := keyV.2.2 ⟨j, by simpa only [ByteArray.size, key.size_toArray] using hj⟩
    rw [rdiV]
    apply Option.isSome_iff_exists.mpr
    refine ⟨(⟨key.toArray⟩ : ByteArray)[j]'(by simpa only [ByteArray.size, key.size_toArray] using hj), ?_⟩
    simpa only [registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hb
  obtain ⟨w, aw, W, ripW, copies⟩ := key_copy hs outside
    ⟨V.ready, V.code, AgreesExcept.refl _ _⟩ growsV ripV spV (rdiV ▸ kb) kr (by
      rw [rdiV]; omega)
  have slotLen : wd u (stackPtr u + 184) = BitVec.ofNat 64 plaintext.size := by
    have he : stackPtr u + 184 = stackPtr initial + BitVec.ofNat 64 (8*(1+1)) := by
      rw [spU]; bv_omega
    rw [he]
    refine (load_outside (U.frame hs) ?_).trans (argument_value len)
    intro i hi
    simp only [Wrapper.wrapperFrame, wrapperFrameBytes, MemoryRegion.Contains,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have r13W : rd w 13 = BitVec.ofNat 64 plaintext.size :=
    (W.agrees.read (by simp [keyCopyChanges])).trans (r13V.trans slotLen)
  have nsmall : plaintext.size < 2^32 := by
    have h : (initial.regValue .rcx).toNat + plaintext.size < 2^32 := hc.inputsInMemory.2.2.2.1.1
    omega
  obtain ⟨t, at', T, ripT, rbpT, zfT⟩ := length_check outside nsmall
    ⟨W.ready, W.code, AgreesExcept.refl _ _⟩ ripW r13W
  have growsW := growsV.step W.agrees
  have growsT := growsW.step T.agrees
  have targetAddr : BitVec.ofNat 64 ((stackPtr initial).toNat - 80) = stackPtr initial - 80 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_sub,
      show (80 : BitVec 64).toNat = 80 from rfl]
    omega
  have keyW : ValidInput w ⟨(stackPtr initial).toNat - 80, 32⟩ ⟨key.toArray⟩ := by
    apply input_of_word_copies keyV key.size_toArray (by change _ - 80 + 32 < 2^32; omega) rfl
    · refine ⟨?_, ?_⟩
      · rw [targetAddr]
        simp only [BitVec.toNat_sub, show (80 : BitVec 64).toNat = 80 from rfl]
        omega
      · intro i hi
        apply growsW
        rw [targetAddr]
        apply hs.allocated
        all_goals
          simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
            show (80 : BitVec 64).toNat = 80 from rfl]
          omega
    · intro j
      rw [targetAddr]
      have hj : memLoad w.external (stackPtr initial - 80 + BitVec.ofNat 64 (8*j.val)) 64 =
          memLoad v.external (rd v 7 + BitVec.ofNat 64 (8*j.val)) 64 := copies j
      simpa only [registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq, rdiV] using hj
  have common := initial_common hc hm hs U V W T (by
    intro k r h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h <;> cases h <;> assumption) keyW
  have pair : List.Pairwise MemoryRegion.Disjoint
      [bufferRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial 1168] := hc.separation.1
  have allocStack : allocatorStateRegion.Disjoint (Stack.region initial 1168) :=
    List.pairwise_pair.mp pair.tail.tail
  have allocKept : ∀ a : BitVec 64, allocatorStateRegion.Contains a.toNat → t.external[a]? = v.external[a]? := by
    intro a ha
    apply (W.agrees.trans T.agrees).byte
    intro c hc'
    simp only [keyCopyChanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
    all_goals first
      | exact nonmem_not_covers rfl _
      | (rintro ⟨i, hi, he⟩; apply allocStack a.toNat ha; rw [he]
         change (stackPtr initial).toNat - 1168 ≤ _ ∧ _ <
           (stackPtr initial).toNat - 1168 + ((stackPtr initial).toNat + 8 -
             ((stackPtr initial).toNat - 1168))
         simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
           show (80 : BitVec 64).toNat = 80 from rfl]
         omega)
  have globalWord {offset : Nat} {value : BitVec 64} (hoff : offset = 0 ∨ offset = 8)
      (hv : wd v (0x300000 + BitVec.ofNat 64 offset) = value) :
      (⟨0x300000 + offset, 8⟩ : MemoryRegion).Word64At t.external value := by
    apply word_preserved (by change 0x300000 + offset + 8 < 2^32; omega)
      (word64At_of_memLoad (fun i hi => ?_) hv (by simp only [BitVec.ofNat_add]; rfl))
    · intro a ha
      apply allocKept a
      change 0x300000 + offset ≤ a.toNat ∧ a.toNat < 0x300000 + offset + 8 at ha
      change 0x300000 ≤ a.toNat ∧ a.toNat < 0x300000 + 16
      omega
    · apply V.agrees.grow
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocMem.mem _ (by omega)
  have capU : wd u (stackPtr u + 192) = memLoad initial.external (stackPtr initial + 24) 64 := by
    have he : stackPtr u + 192 = stackPtr initial + 24 := by rw [spU]; bv_omega
    rw [he]
    apply load_outside (U.frame hs)
    intro i hi
    simp only [Wrapper.wrapperFrame, wrapperFrameBytes, MemoryRegion.Contains,
      BitVec.toNat_add, BitVec.toNat_ofNat, show (24 : BitVec 64).toNat = 24 from rfl]
    omega
  refine ⟨25, t, au.trans (av.trans (aw.trans at')), {
    toCommon := common
    rip := ripT
    rsp := sp_keep T.agrees (by simp) (sp_keep W.agrees (by simp [keyCopyChanges]) spV)
    rbp := rbpT
    r12 := ?_
    r13 := (T.agrees.read (by simp)).trans r13W
    rsi := ?_
    rdx := ?_
    r9 := ?_
    zf := zfT
    allocator := ?_
    limit := ?_ }⟩
  · exact (T.agrees.read (by simp)).trans
      ((W.agrees.read (by simp [keyCopyChanges])).trans (r12V.trans (regsU 1 (by decide))))
  · exact (T.agrees.read (by simp)).trans ((W.agrees.read (by simp [keyCopyChanges])).trans
      ((V.agrees.read (by simp [allocatorChanges])).trans (regsU 6 (by decide))))
  · exact (T.agrees.read (by simp)).trans ((W.agrees.read (by simp [keyCopyChanges])).trans
      ((V.agrees.read (by simp [allocatorChanges])).trans (regsU 2 (by decide))))
  · exact (T.agrees.read (by simp)).trans ((W.agrees.read (by simp [keyCopyChanges])).trans
      ((V.agrees.read (by simp [allocatorChanges])).trans (regsU 9 (by decide))))
  · apply globalWord (offset := 0) (Or.inl rfl)
    change wd v 0x300000 = rd initial 8
    exact headV.trans (regsU 8 (by decide))
  · apply globalWord (offset := 8) (Or.inr rfl)
    change wd v 0x300008 = _
    rw [limitV, capU, regsU 8 (by decide)]
    rfl

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
