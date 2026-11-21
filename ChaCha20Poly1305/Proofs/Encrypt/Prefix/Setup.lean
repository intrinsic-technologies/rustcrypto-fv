import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Memory
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Setup.Run

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract Wrapper

theorem setup_to_core [bindings : Bindings] {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (_hb : MachineRamUnitStrideDecodable bindings initial)
    (_hm : SupportedIntegerMachineState bindings.processor initial)
    (hc : ValidCall encrypt initial [key, nonce, associatedData, plaintext]) {s : RamState}
    (hs : BeforeCoreSetup initial s key plaintext) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      CoreState initial t key plaintext := by
  have hS : Stack.Valid initial 1168 := hc.stackAvailable
  obtain ⟨room, top⟩ := stack_bounds hS
  have hA := hc.separation.2.2 (Stack.region initial 1168)
    (by simp [writtenRegions, encrypt])
  have slot : StackArgument initial 0 (BitVec.ofNat 64 associatedData.size) :=
    hc.lengthArgumentsMatchInputs.2.2.1
  have addr : BitVec.ofNat 64 (stackArgumentSlot initial 0).start = stackPtr initial + 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [stackArgumentSlot, show initial.regValue .rsp = stackPtr initial from rfl,
      BitVec.toNat_ofNat, BitVec.toNat_add]
    rfl
  have slotKept : ∀ a : BitVec 64, (stackArgumentSlot initial 0).Contains a.toNat →
      s.external[a]? = initial.external[a]? := by
    intro a ha
    apply hs.frame
    intro r hr ar
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    have read : stackArgumentSlot initial 0 ∈
        readRegions encrypt initial [key, nonce, associatedData, plaintext] := by
      simp [readRegions, encrypt, argumentRegions]
    rcases hr with rfl | rfl | rfl
    · exact hc.separation.2.1 _ (by simp [writtenRegions, encrypt]) _ read _ ar ha
    · exact hc.separation.2.1 _ (by simp [writtenRegions, encrypt]) _ read _ ar ha
    · change (stackPtr initial).toNat - 176 ≤ a.toNat ∧
        a.toNat < (stackPtr initial).toNat - 176 + 176 at ar
      change (initial.regValue .rsp).toNat + 8 * (0 + 1) ≤ a.toNat ∧ _ at ha
      change (stackPtr initial).toNat + 8 * (0 + 1) ≤ a.toNat ∧ _ at ha
      omega
  have slotS := word_preserved slot.1 slot.2 slotKept
  have hRead : MemReadable s (stackPtr initial + 8) 8 := by
    refine ⟨?_, ?_⟩
    · have low := slot.1
      change (stackPtr initial).toNat + 8 + 8 < 2 ^ 32 at low
      simp only [BitVec.toNat_add, BitVec.reduceToNat]
      omega
    · rw [← addr]
      exact loadBytes_isSome slotS.2
  have outside : ¬ InProgram (returnBoundary initial).rip := by
    obtain ⟨address, hs, _, ho⟩ := hc.returnAddress
    have h := word64At_memLoad hs
    simp only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    change ¬ InProgram (wd initial (stackPtr initial))
    rw [show wd initial (stackPtr initial) = address from h]
    exact ho
  obtain ⟨fuel, t, adv, tr, rip, rsp, rdi, rsi, r9, rdx, rcx, r8,
      w152, w104, w96, w88, w176⟩ :=
    setup_run hS hA hs.grows hs.ready hs.code outside hs.rip hs.rsp hRead
  have wr : WritesWithin (setupChanges initial)
      #v[(⟨(stackPtr initial).toNat - 176, 176⟩ : MemoryRegion)] := by
    intro c mem a cov
    simp only [setupChanges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd cov (nonmem_not_covers rfl _)
      | refine ⟨(⟨(stackPtr initial).toNat - 176, 176⟩ : MemoryRegion), by simp, ?_⟩
        obtain ⟨i, hi, rfl⟩ := cov
        simp only [MemoryRegion.Contains]
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat]
        constructor <;> omega
  have frame := tr.agrees.memoryWriteFrame wr
  have frameAll : MemoryWriteFrame s t
      #v[heapRegion encrypt initial, allocatorStateRegion,
        ⟨(stackPtr initial).toNat - 176, 176⟩] := by
    intro a ha
    apply frame a
    intro r hr ar
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    exact ha _ (by simp) ar
  have keep (a : BitVec 64)
      (apart : ∀ k ∈ [152, 104, 96, 88, 176],
        a.toNat < (stackPtr initial).toNat - k ∨
          (stackPtr initial).toNat - k + 8 ≤ a.toNat) :
      t.external[a]? = s.external[a]? := by
    apply tr.agrees.byte
    intro c mem
    simp only [setupChanges, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact nonmem_not_covers rfl _
      | rintro ⟨i, hi, eq⟩
        have ap1 := apart 152 (by simp)
        have ap2 := apart 104 (by simp)
        have ap3 := apart 96 (by simp)
        have ap4 := apart 88 (by simp)
        have ap5 := apart 176 (by simp)
        rw [eq] at ap1 ap2 ap3 ap4 ap5
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
          BitVec.reduceToNat] at ap1 ap2 ap3 ap4 ap5
        omega
  have common := hs.toCommon.step (by omega) top tr.agrees (by simp [setupChanges])
    tr.ready tr.code frameAll (by
      intro a lo hi
      apply keep
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega)
  have keptWord {k : Nat} {v : BitVec 64} (hk : k ∈ [168,160])
      (hw : (localWord initial k).Word64At s.external v) :
      (localWord initial k).Word64At t.external v := by
    apply word_preserved (by
      change (stackPtr initial).toNat - k + 8 < 2 ^ 32
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> omega) hw
    intro a ha
    apply keep
    intro j hj
    change (stackPtr initial).toNat - k ≤ a.toNat ∧
      a.toNat < (stackPtr initial).toNat - k + 8 at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk hj
    rcases hk with rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega
  have newWord {k : Nat} {v : BitVec 64} (hk : 8 ≤ k) (hk' : k ≤ 176)
      (hw : wd t (stackPtr initial - BitVec.ofNat 64 k) = v) :
      (localWord initial k).Word64At t.external v := by
    apply word64At_of_memLoad (a := stackPtr initial - BitVec.ofNat 64 k)
      (stack_slot_readable hS (fun a ha => tr.agrees.grow a (hs.grows a ha))
        (by omega)).mem hw
    apply BitVec.eq_of_toNat_eq
    rw [slot_toNat0 (by omega), BitVec.toNat_ofNat]
    change ((stackPtr initial).toNat - k) % 2 ^ 64 = _
    omega
  have vals : rd s 5 + rd s 13 = BitVec.ofNat 64 plaintext.size := by
    change s.regValue .rbp + s.regValue .r13 = _
    rw [hs.rbp, hs.r13]
    exact BitVec.zero_add _
  have pointer : wd s (stackPtr initial - 160) = initial.regValue .r8 := by
    have h := word64At_memLoad hs.pointer
    have addr : BitVec.ofNat 64 (localWord initial 160).start = stackPtr initial - 160 := by
      apply BitVec.eq_of_toNat_eq
      rw [show (stackPtr initial - 160).toNat = (stackPtr initial).toNat - 160 from
        slot_toNat0 (k := 160) (by omega), BitVec.toNat_ofNat]
      change ((stackPtr initial).toNat - 160) % 2 ^ 64 = _
      omega
    rw [addr] at h
    exact h
  have msg : ValidInput t (messageRegion (initial.regValue .r8) plaintext.size) plaintext := by
    apply input_preserved hs.message
    intro a ha
    apply frame a
    intro r hr ar
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    have pair := hc.separation.1
    have wrs : writtenRegions encrypt initial [key, nonce, associatedData, plaintext] =
      [bufferRegion encrypt initial, heapRegion encrypt initial, allocatorStateRegion,
        Stack.region initial 1168] := rfl
    rw [wrs] at pair
    have sep := (List.pairwise_cons.mp pair.tail).1 (Stack.region initial 1168) (by simp)
    apply sep a.toNat
    · rw [heap_region hc]
      change (initial.regValue .r8).toNat ≤ a.toNat ∧
        a.toNat < (initial.regValue .r8).toNat + (plaintext.size + 16)
      change (initial.regValue .r8).toNat ≤ a.toNat ∧
        a.toNat < (initial.regValue .r8).toNat + plaintext.size at ha
      constructor <;> omega
    · change (stackPtr initial).toNat - 1168 ≤ a.toNat ∧
        a.toNat < (stackPtr initial).toNat - 1168 +
          ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
      change (stackPtr initial).toNat - 176 ≤ a.toNat ∧
        a.toNat < (stackPtr initial).toNat - 176 + 176 at ar
      constructor <;> omega
  refine ⟨fuel, t, adv,
    { toCommon := common
      atCore := ?_
      rip := rip
      rsi := ?_
      rdx := ?_
      rcx := ?_
      r8 := ?_
      r9 := ?_
      input := newWord (by omega) (by omega) (w104.trans pointer)
      output := newWord (by omega) (by omega) (w96.trans pointer)
      lengthWord := newWord (by omega) (by omega) (w88.trans vals)
      message := msg }⟩
  · exact
      { rsp := rsp
        returnAddress := by change wd t (stackPtr t) = _; rw [rsp]; exact w176
        result := rdi
        rbx := by
          change rd t 3 = _
          rw [rd, tr.agrees.read (by simp [setupChanges])]
          exact hs.rbx
        capacity := keptWord (by simp) hs.capacity
        pointer := keptWord (by simp) hs.pointer
        lengthWord := newWord (by omega) (by omega) (w152.trans vals)
        savedRbp := common.savedRbp
        savedR15 := common.savedR15
        savedR14 := common.savedR14
        savedR13 := common.savedR13
        savedR12 := common.savedR12
        savedRbx := common.savedRbx
        frame := common.frame
        grows := common.grows }
  · exact rsi
  · change t.regValue .rdx = s.regValue .r15 at rdx
    exact rdx.trans hs.r15
  · change t.regValue .rcx = s.regValue .r14 at rcx
    exact rcx.trans hs.r14
  · change t.regValue .r8 = wd s (stackPtr initial + 8) at r8
    rw [r8]
    apply memLoad_congr
    intro i hi
    change i < 8 at hi
    simp only [memByte]
    congr 1
    exact slotKept _ (by
      rw [← addr]
      simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat, stackArgumentSlot,
        show initial.regValue .rsp = stackPtr initial from rfl]
      omega)
  · exact r9

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
