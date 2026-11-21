import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Dispatch
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Return

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper CoreContract

set_option maxHeartbeats 800000 in
theorem dispatch_to_setup [bindings : Bindings] {initial s : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (st : EntryStack initial) (outside : ¬ InProgram (returnBoundary initial).rip)
    (hs : BeforeCopy initial s key msg.size) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ BeforeCoreSetup initial t key msg := by
  have room := st.room
  have top := st.top
  have hlo := (hc.heapInMemory rfl).1.1
  rw [heap_region hc] at hlo
  change (initial.regValue .r8).toNat + (msg.size + 16) < 2^32 at hlo
  have bound : msg.size < 2^32 := by omega
  by_cases hz : msg.size = 0
  · refine ⟨0, s, (advances_zero _ _ _).mpr rfl, ⟨hs.toCommon, ?_, hs.rsp, hs.rbp, hs.r13,
      hs.r14, hs.r15, hs.rbx, hs.capacity, hs.pointer, ?_⟩⟩
    · simpa only [hz, ite_true] using hs.rip
    · refine ⟨?_, rfl, fun i => ?_⟩
      · change (initial.regValue .r8).toNat + msg.size < 2^32
        have h := (hc.heapInMemory rfl).1.1
        rw [heap_region hc] at h
        change (initial.regValue .r8).toNat + (msg.size + 16) < 2^32 at h
        omega
      · have := i.isLt; omega
  · have pos : 0 < msg.size := by omega
    obtain ⟨u, au, tu, ripu, rspu, dstu, srcu, lenu, retu⟩ := call_copy st hs.grows outside
      ⟨hs.ready, hs.code, AgreesExcept.refl _ _⟩ (by simpa only [hz, ite_false] using hs.rip)
      hs.rsp hs.rbp
    have commonu : Common initial u key := hs.toCommon.stack_step st tu (by simp [copySetupChanges]) (by
      intro c hcm a ha
      simp only [copySetupChanges, List.mem_cons, List.not_mem_nil, or_false] at hcm
      rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact ha.elim
      obtain ⟨i, hi, rfl⟩ := ha
      exact stack_component_bounds st (by omega) (by omega) hi)
    have dst : rdi.read u = initial.regValue .r8 := dstu.trans hs.rdi
    have src : rsi.read u = initial.regValue .rcx := srcu.trans hs.r12
    have len : MemoryContracts.rdx.read u = BitVec.ofNat 64 msg.size := lenu.trans hs.r13
    have lenn : (MemoryContracts.rdx.read u).toNat = msg.size := by
      rw [len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have ret : (returnBoundary u).rip = 0x101828 := by
      change wd u (stackPtr u) = _
      rw [rspu]; exact retu
    have pre := copy_pre hc commonu st pos ripu rspu ret dst src len
    obtain ⟨n, t, adv, post⟩ := MemoryContracts.memcpy_advances hb.stringStride
      (returnBoundary initial) (outside_memcpy outside) u commonu.ready commonu.code pre
      (by rw [ret]; exact code_ne_boundary outside 0x1828 (by omega))
    have commont := commonu.copy_step hc st post dst lenn
    have ru (r : BitVec 5) (h : .reg r ∉ copySetupChanges (stackPtr initial)) : rd u r = rd s r :=
      tu.agrees.read h
    have rt (r : BitVec 5) (h : .reg r ∉ MemoryRoutines.callChanges u) : rd t r = rd u r :=
      post.agrees.read h
    have word {k : Nat} {v : BitVec 64} (hk : 8 ≤ k) (hk' : k ≤ 168)
        (hw : (localWord initial k).Word64At s.external v) :
        (localWord initial k).Word64At t.external v := by
      apply word_preserved (by change _ - k + 8 < 2^32; omega)
        (copy_setup_word st hk hk' tu.agrees hw)
      intro a ha
      apply copy_stack_eq hc post dst lenn a
      change (stackPtr initial).toNat - k ≤ a.toNat ∧ a.toNat < (stackPtr initial).toNat - k + 8 at ha
      change (stackPtr initial).toNat - 1168 ≤ a.toNat ∧ a.toNat <
        (stackPtr initial).toNat - 1168 +
          ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
      have hr : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
      omega
    refine ⟨4 + n, t, au.trans adv, ⟨commont, post.rip.trans ret, ?_, ?_, ?_, ?_, ?_, ?_,
      word (by omega) (by omega) hs.capacity, word (by omega) (by omega) hs.pointer, ?_⟩⟩
    · rw [post.rsp, rspu]; bv_omega
    · exact (rt 5 (by simp [MemoryRoutines.callChanges])).trans
        ((ru 5 (by simp [copySetupChanges])).trans hs.rbp)
    · exact (rt 13 (by simp [MemoryRoutines.callChanges])).trans
        ((ru 13 (by simp [copySetupChanges])).trans hs.r13)
    · exact (rt 14 (by simp [MemoryRoutines.callChanges])).trans
        ((ru 14 (by simp [copySetupChanges])).trans hs.r14)
    · exact (rt 15 (by simp [MemoryRoutines.callChanges])).trans
        ((ru 15 (by simp [copySetupChanges])).trans hs.r15)
    · exact (rt 3 (by simp [MemoryRoutines.callChanges])).trans
        ((ru 3 (by simp [copySetupChanges])).trans hs.rbx)
    · have hi := original_input hc commonu.frame
        (r := registerRegion initial .rcx msg.size) (by simp [readRegions, encrypt, inputRegion])
        hc.inputsInMemory.2.2.2.1
      have hi' : ValidInput u (registerRegion u .rsi msg.size) msg := by
        change ValidInput u ⟨(rsi.read u).toNat, msg.size⟩ msg
        rw [src]; exact hi
      have hp := copied_input hi' (by rw [dst]; omega) lenn post
      rw [dst] at hp
      exact hp

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
