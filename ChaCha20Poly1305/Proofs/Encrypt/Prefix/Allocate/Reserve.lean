import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.State
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Bounds
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Reserve.Save
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Reserve.Claim
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Memory
import ChaCha20Poly1305.Proofs.Encrypt.Suffix.Facts

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper MemoryRoutines.Machine

set_option maxHeartbeats 1000000 in
 theorem alloc_to_header [bindings : Bindings] {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad plaintext : ByteArray}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hc : ValidCall encrypt initial [key, nonce, aad, plaintext]) {s : RamState}
    (hs : BeforeAlloc initial s key plaintext.size) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      BeforeHeader initial t key plaintext.size := by
  have _ := hb
  have _ := hm
  have st := Suffix.entry_stack hc
  have room := st.room
  have top := st.top
  have outside : ¬ InProgram (returnBoundary initial).rip := by
    obtain ⟨addr, hw, -, ha⟩ := hc.returnAddress
    have he := word64At_memLoad hw
    simp only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] at he
    have he' : (returnBoundary initial).rip = addr := he
    rw [he']
    exact ha
  have allocMem : allocatorStateRegion ∈ writtenRegions encrypt initial [key, nonce, aad, plaintext] := by
    simp [writtenRegions, encrypt]
  have apart : allocatorStateRegion.Disjoint (Stack.region initial 1168) := by
    have h := hc.separation.1
    change [_ , _, allocatorStateRegion, Stack.region initial 1168].Pairwise MemoryRegion.Disjoint at h
    exact (List.pairwise_cons.mp h.tail.tail).1 _ (by simp)
  have slotAvoid {x : BitVec 64} (hx : allocatorStateRegion.Contains x.toNat) :
      ¬ (Component.mem (stackPtr initial - 176) 8).Covers x := by
    rintro ⟨i, hi, he⟩
    apply apart x.toNat hx
    rw [he]
    have hr := hc.stackAvailable.2.2.1
    change _ - 1168 ≤ _ ∧ _ < _ - 1168 + (_ + 8 - (_ - 1168))
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat]
    change 1168 ≤ (stackPtr initial).toNat at hr
    simp only [show initial.regValue .rsp = stackPtr initial from rfl]
    omega
  obtain ⟨u, a, T, rip, sp, bx, r14, r15⟩ := reserve_save st hs.grows outside
    ⟨hs.ready, hs.code, AgreesExcept.refl _ _⟩ hs.rip hs.rsp hs.zf
  have keepAlloc (x : BitVec 64) (hx : allocatorStateRegion.Contains x.toNat) :
      u.external[x]? = s.external[x]? := by
    apply T.agrees.byte
    intro c hc'
    simp only [saveChanges, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact nonmem_not_covers rfl _ | exact slotAvoid hx
  have cursor : wd u 0x300000 = initial.regValue .r8 := by
    have hw := word_preserved (s := s) (t := u) (by change 0x300000 + 8 < 2^32; decide)
      hs.allocator (fun x hx => keepAlloc x ⟨hx.1, by have ht : x.toNat < 0x300008 := hx.2; change x.toNat < 0x300010; omega⟩)
    exact word64At_memLoad (region := ⟨0x300000, 8⟩) hw
  have limit : wd u 0x300008 =
      (if (initial.regValue .r8).toNat + (memLoad initial.external (stackPtr initial + 24) 64).toNat < 2^64
      then initial.regValue .r8 + memLoad initial.external (stackPtr initial + 24) 64 else BitVec.allOnes 64) := by
    have hw := word_preserved (s := s) (t := u) (by change 0x300008 + 8 < 2^32; decide)
      hs.limit (fun x hx => keepAlloc x ⟨by have ht : 0x300008 ≤ x.toNat := hx.1; change 0x300000 ≤ x.toNat; omega, hx.2⟩)
    exact word64At_memLoad (region := ⟨0x300008, 8⟩) hw
  have rd5 : rd u 5 = BitVec.ofNat 64 (plaintext.size + 16) :=
    (T.agrees.read (by simp [saveChanges])).trans hs.rbp
  have read0 : MemReadable u 0x300000 8 :=
    ⟨by decide, fun i hi => T.agrees.grow _ (loadBytes_isSome hs.allocator.2 i hi)⟩
  have read8 : MemReadable u 0x300008 8 :=
    ⟨by decide, fun i hi => T.agrees.grow _ (loadBytes_isSome hs.limit.2 i hi)⟩
  have av (x : BitVec 64) (hx : (Component.mem 0x300000 8).Covers x) : ¬ InProgram x := by
    apply fun hp => hc.separation.2.2 _ allocMem x ?_ (.inl hp)
    obtain ⟨i, hi, rfl⟩ := hx
    change 0x300000 ≤ _ ∧ _ < 0x300010
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega
  obtain ⟨small, nz, cap⟩ := allocation_bounds hc
  have noWrap : (initial.regValue .r8).toNat + (BitVec.ofNat 64 (plaintext.size + 16)).toNat < 2^64 := by
    simp only [BitVec.toNat_ofNat]
    omega
  obtain ⟨t, b, U, ripT, di⟩ := reserve_claim outside
    ⟨T.ready, T.code, AgreesExcept.refl _ _⟩ rip rd5 cursor limit read0 read8
    ⟨read0.low, read0.mem, by decide⟩ av noWrap (allocation_limit small cap) nz
  have agree := T.agrees.trans U.agrees
  have common : Common initial t key := by
    apply hs.toCommon.step (by omega) top agree (by simp [saveChanges, claimChanges]) U.ready U.code
    · apply agree.memoryWriteFrame
      intro c hmem x hx
      simp only [List.mem_append, saveChanges, claimChanges, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hmem | hmem
      · rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact False.elim (nonmem_not_covers rfl _ hx)
        refine ⟨⟨(stackPtr initial).toNat - 176, 176⟩, by simp, ?_⟩
        obtain ⟨i, hi, rfl⟩ := hx
        change _ ≤ _ ∧ _ < _
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
      · rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact False.elim (nonmem_not_covers rfl _ hx)
        refine ⟨allocatorStateRegion, by simp, ?_⟩
        obtain ⟨i, hi, rfl⟩ := hx
        change 0x300000 ≤ _ ∧ _ < 0x300010
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
        omega
    · intro x hlo hhi
      apply agree.byte
      intro c hmem
      simp only [List.mem_append, saveChanges, claimChanges, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hmem | hmem
      · rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact nonmem_not_covers rfl _
        apply mem_not_covers
        · right
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
          omega
        · simp only [BitVec.toNat_sub, BitVec.reduceToNat]; omega
      · rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact nonmem_not_covers rfl _
        rintro ⟨i, hi, he⟩
        apply apart x.toNat
        · rw [he]
          change 0x300000 ≤ _ ∧ _ < 0x300010
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega
        · have hr := hc.stackAvailable.2.2.1
          change (stackPtr initial).toNat - 1168 ≤ x.toNat ∧ x.toNat <
            (stackPtr initial).toNat - 1168 + ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
          change 1168 ≤ (stackPtr initial).toNat at hr
          omega
  refine ⟨_, t, a.trans b, {
    toCommon := common
    rip := ripT
    rsp := sp_keep U.agrees (by simp [claimChanges]) sp
    rbp := (U.agrees.read (by simp [claimChanges])).trans rd5
    r12 := ?_
    r13 := ?_
    r14 := ?_
    r15 := ?_
    rbx := ?_
    rdi := di }⟩
  · exact (agree.read (n := 64) (r := 12) (by simp [saveChanges, claimChanges])).trans hs.r12
  · exact (agree.read (n := 64) (r := 13) (by simp [saveChanges, claimChanges])).trans hs.r13
  · exact (U.agrees.read (by simp [claimChanges])).trans (r14.trans hs.rdx)
  · exact (U.agrees.read (by simp [claimChanges])).trans (r15.trans hs.rsi)
  · exact (U.agrees.read (by simp [claimChanges])).trans (bx.trans hs.r9)

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
