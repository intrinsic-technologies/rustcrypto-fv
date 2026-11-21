import ChaCha20Poly1305.Proofs.Encrypt.Prefix.State
import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract Wrapper

theorem core_pre [bindings : Bindings] {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (_hm : SupportedIntegerMachineState bindings.processor initial)
    (hc : ValidCall encrypt initial [key, nonce, associatedData, plaintext]) {s : RamState}
    (hs : CoreState initial s key plaintext) :
    CorePre s key nonce associatedData plaintext (initial.regValue .r8)
      (initial.regValue .r8) := by
  have room : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
  have top : (stackPtr initial).toNat + 8 < 2 ^ 32 := by
    have h := hc.stackAvailable.1
    change (stackPtr initial).toNat - 1168 +
      ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168)) < 2 ^ 32 at h
    omega
  let St : MemoryRegion := ⟨(stackPtr initial).toNat - 1168, 1176⟩
  let Heap := heapRegion encrypt initial
  have stEq : Stack.region initial 1168 = St := stack_region_eq _ _ room
  have wr : writtenRegions encrypt initial [key, nonce, associatedData, plaintext] =
      [bufferRegion encrypt initial, Heap, allocatorStateRegion, St] := by
    change [_, _, _, Stack.region initial 1168] = _
    rw [stEq]
  have stMem : St ∈ writtenRegions encrypt initial [key, nonce, associatedData, plaintext] := by
    rw [wr]; simp
  have heapMem : Heap ∈ writtenRegions encrypt initial [key, nonce, associatedData, plaintext] := by
    rw [wr]; simp
  have allocMem : allocatorStateRegion ∈
      writtenRegions encrypt initial [key, nonce, associatedData, plaintext] := by
    rw [wr]; simp
  have heapSt : Heap.Disjoint St := by
    have h := hc.separation.1
    rw [wr] at h
    exact (List.pairwise_cons.mp h.tail).1 _ (by simp)
  have subSt : ∀ (r : MemoryRegion), (stackPtr initial).toNat - 1168 ≤ r.start →
      r.start + r.size ≤ (stackPtr initial).toNat + 8 →
      ∀ x, r.Contains x → St.Contains x := by
    intro r lo hi x hx
    simp only [MemoryRegion.Contains, St] at hx ⊢
    omega
  have allocSt : ∀ {r : MemoryRegion},
      (∀ x, r.Contains x → St.Contains x) → r.Allocated s.external := by
    intro r sub a ha
    obtain ⟨b, hb'⟩ := hc.stackAvailable.2.1 a (by
      change (Stack.region initial 1168).Contains a.toNat
      rw [stEq]
      exact sub _ ha)
    exact Option.isSome_iff_exists.mp (hs.grows a (by simp only [hb', Option.isSome_some]))
  have readMem : ∀ r, r = registerRegion initial .rsi 12 ∨
      r = registerRegion initial .rdx associatedData.size →
      r ∈ readRegions encrypt initial [key, nonce, associatedData, plaintext] := by
    intro r hr
    rcases hr with rfl | rfl <;> simp [readRegions, encrypt, inputRegion]
  have kept : ∀ {r : MemoryRegion} {bytes : ByteArray},
      (r = registerRegion initial .rsi 12 ∨ r = registerRegion initial .rdx associatedData.size) →
      ValidInput initial r bytes → ValidInput s r bytes := by
    intro r bytes hr hin
    refine ⟨hin.1, hin.2.1, fun i => ?_⟩
    rw [hs.frame _ ?_]
    · exact hin.2.2 i
    intro w hw ha
    have mem : r.Contains (BitVec.ofNat 64 (r.start + i.val)).toNat := by
      have bound := hin.1
      have len := hin.2.1
      have hi := i.isLt
      simp only [MemoryRegion.Bounded, userAddressLimit, MemoryRegion.HasLength] at bound len
      simp only [MemoryRegion.Contains, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      constructor <;> omega
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact hc.separation.2.1 _ heapMem _ (readMem _ hr) _ ha mem
    · exact hc.separation.2.1 _ allocMem _ (readMem _ hr) _ ha mem
    · exact hc.separation.2.1 _ stMem _ (readMem _ hr) _
        (subSt _ (by simp only; omega) (by simp only; omega) _ ha) mem
  obtain ⟨hKey, hNonce, hAD, hPlain, -⟩ := hc.inputsInMemory
  have hADslot : StackArgument initial 0 (BitVec.ofNat 64 associatedData.size) :=
    hc.lengthArgumentsMatchInputs.2.2.1
  have hADword := word64At_memLoad hADslot.2
  have adBound : (initial.regValue .rdx).toNat + associatedData.size < 2 ^ 32 := hAD.1
  have hADlen : (s.regValue .r8).toNat = associatedData.size := by
    rw [hs.r8]
    have addr : BitVec.ofNat 64 (stackArgumentSlot initial 0).start = stackPtr initial + 8 := by
      simp only [stackArgumentSlot]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
      change ((stackPtr initial).toNat + 8 + 8 * 0) % 2 ^ 64 =
        ((stackPtr initial).toNat + (8 : BitVec 64).toNat) % 2 ^ 64
      rfl
    rw [addr] at hADword
    rw [hADword, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hIs : (stackPtr s).toNat = (stackPtr initial).toNat - 176 := by
    rw [hs.atCore.rsp]
    exact slot_toNat0 (k := 176) (by omega)
  have hrdiN : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 137 := by
    rw [hs.atCore.result]
    exact slot_toNat0 (k := 137) (by omega)
  have hrsiN : (s.regValue .rsi).toNat = (stackPtr initial).toNat - 80 := by
    rw [hs.rsi]
    exact slot_toNat0 (k := 80) (by omega)
  have hr9N : (s.regValue .r9).toNat = (stackPtr initial).toNat - 104 := by
    rw [hs.r9]
    exact slot_toNat0 (k := 104) (by omega)
  have hStS : Stack.region s coreStackBytes = ⟨(stackPtr initial).toNat - 1168, 1000⟩ := by
    simp only [Stack.region, Stack.returnAddressBytes, coreStackBytes,
      show s.regValue .rsp = stackPtr s from rfl, hIs, MemoryRegion.mk.injEq]
    constructor <;> omega
  have hRes : resultRegion s = ⟨(stackPtr initial).toNat - 137, 17⟩ := by
    simp only [resultRegion, registerRegion, resultBytes, hrdiN]
  have hKeyR : keyRegion s = ⟨(stackPtr initial).toNat - 80, 32⟩ := by
    simp only [keyRegion, registerRegion, hrsiN]
  have hNonceR : nonceRegion s = registerRegion initial .rsi 12 := by
    simp only [nonceRegion, registerRegion, hs.rdx]
  have hADR : associatedDataRegion s = registerRegion initial .rdx associatedData.size := by
    simp only [associatedDataRegion, registerRegion, hs.rcx, hADlen]
  have hDescR : descriptorRegion s = ⟨(stackPtr initial).toNat - 104, 24⟩ := by
    simp only [descriptorRegion, registerRegion, hr9N]
  have msgSub : ∀ x, (messageRegion (initial.regValue .r8) plaintext.size).Contains x →
      Heap.Contains x := by
    dsimp only [Heap]
    rw [heap_region hc]
    intro x hx
    simp only [messageRegion, registerRegion, MemoryRegion.Contains] at hx ⊢
    constructor <;> omega
  refine
    { environment := ⟨hs.ready.smrr, hs.ready.memoryType, hb.stringStride, hs.ready.features.lzcnt⟩
      machine := hs.machine
      code := hs.code
      entry := hs.rip
      directionFlagUnset := hs.direction
      stack := ?_
      keyInMemory := by rw [hKeyR]; exact hs.keyBytes
      nonceInMemory := by rw [hNonceR]; exact kept (.inl rfl) hNonce
      associatedDataLength := hADlen
      associatedDataInMemory := by rw [hADR]; exact kept (.inr rfl) hAD
      descriptorBounded := by rw [hDescR]; simp only [MemoryRegion.Bounded, userAddressLimit]; omega
      inPointer := ?_
      outPointer := ?_
      messageLength := ?_
      messageInMemory := hs.message
      outputInMemory := ?_
      inPlaceOrApart := .inl rfl
      resultInMemory := ?_
      separation := ?_ }
  · have al := hc.stackAvailable.2.2.2
    simp only [Stack.returnSlot, MemoryRegion.Aligned, Stack.callAlignment,
      Stack.returnAddressBytes] at al
    change (stackPtr initial).toNat % 16 = 8 at al
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (Stack.region s coreStackBytes).Bounded
      rw [hStS]; simp only [MemoryRegion.Bounded, userAddressLimit]; omega
    · change (Stack.region s coreStackBytes).Allocated s.external
      rw [hStS]; exact allocSt (subSt _ (by simp only; omega) (by simp only; omega))
    · simp only [Stack.NoUnderflow, show s.regValue .rsp = stackPtr s from rfl, hIs,
        coreStackBytes]; omega
    · simp only [Stack.returnSlot, MemoryRegion.Aligned, Stack.callAlignment,
        Stack.returnAddressBytes, show s.regValue .rsp = stackPtr s from rfl, hIs]; omega
  · simpa only [descriptorWord, hr9N, Nat.mul_zero, Nat.add_zero, localWord] using hs.input
  · have heq : descriptorWord s 1 = localWord initial 96 := by
      simp only [descriptorWord, hr9N, localWord, MemoryRegion.mk.injEq, and_true]
      omega
    rw [heq]
    exact hs.output
  · have heq : descriptorWord s 2 = localWord initial 88 := by
      simp only [descriptorWord, hr9N, localWord, MemoryRegion.mk.injEq, and_true]
      omega
    rw [heq]
    exact hs.lengthWord
  · refine ⟨hs.message.1, ?_⟩
    exact allocated_kept hs.grows (fun a ha => (hc.heapInMemory rfl).1.2 a (msgSub _ ha))
  · rw [hRes]
    exact ⟨by simp only [MemoryRegion.Bounded, userAddressLimit]; omega,
      allocSt (subSt _ (by simp only; omega) (by simp only; omega))⟩
  ·
    have sR := subSt ⟨(stackPtr initial).toNat - 137, 17⟩ (by simp only; omega)
      (by simp only; omega)
    have sS := subSt ⟨(stackPtr initial).toNat - 1168, 1000⟩ (by simp only; omega)
      (by simp only; omega)
    have sK := subSt ⟨(stackPtr initial).toNat - 80, 32⟩ (by simp only; omega)
      (by simp only; omega)
    have sD := subSt ⟨(stackPtr initial).toNat - 104, 24⟩ (by simp only; omega)
      (by simp only; omega)
    have hStBuf : St.Disjoint Heap := fun x h1 h2 => heapSt x h2 h1
    have hBufSt := heapSt
    have hStNonce := hc.separation.2.1 _ stMem _ (readMem _ (.inl rfl))
    have hStAD := hc.separation.2.1 _ stMem _ (readMem _ (.inr rfl))
    have hBufNonce := hc.separation.2.1 _ heapMem _ (readMem _ (.inl rfl))
    have hBufAD := hc.separation.2.1 _ heapMem _ (readMem _ (.inr rfl))
    have hAvSt := hc.separation.2.2 _ stMem
    have hAvBuf := hc.separation.2.2 _ heapMem
    have hid : ∀ (r : MemoryRegion) x, r.Contains x → r.Contains x := fun _ _ h => h
    simp only [MemorySeparation, coreWritten, coreRead, ite_true, List.append_nil, hRes,
      hStS, hKeyR, hNonceR, hADR, hDescR]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
      exact ⟨⟨disjoint_mono hStBuf sR msgSub,
        disjoint_of_sep (by simp only; omega)⟩, disjoint_mono hBufSt msgSub sS,
        fun _ h => h.elim⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨⟨disjoint_of_sep (by simp only; omega), disjoint_mono hStNonce sR (hid _),
        disjoint_mono hStAD sR (hid _), disjoint_of_sep (by simp only; omega)⟩,
        ⟨disjoint_mono hBufSt msgSub sK, disjoint_mono hBufNonce msgSub (hid _),
        disjoint_mono hBufAD msgSub (hid _), disjoint_mono hBufSt msgSub sD⟩,
        ⟨disjoint_of_sep (by simp only; omega), disjoint_mono hStNonce sS (hid _),
        disjoint_mono hStAD sS (hid _), disjoint_of_sep (by simp only; omega)⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨avoids_mono hAvSt sR, avoids_mono hAvBuf msgSub, avoids_mono hAvSt sS⟩

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
