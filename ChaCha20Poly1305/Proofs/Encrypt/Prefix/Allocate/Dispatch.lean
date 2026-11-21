import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.State
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Header
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.LengthCheck
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Preserve

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper

structure BeforeCopy [Bindings] (initial s : RamState) (key : Vector UInt8 32)
    (length : Nat) : Prop extends Common initial s key where
  rip : s.RIP = if length = 0 then 0x101828 else 0x101819
  rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 168
  rbp : s.regValue .rbp = 0
  r12 : s.regValue .r12 = initial.regValue .rcx
  r13 : s.regValue .r13 = BitVec.ofNat 64 length
  r14 : s.regValue .r14 = initial.regValue .rdx
  r15 : s.regValue .r15 = initial.regValue .rsi
  rbx : s.regValue .rbx = initial.regValue .r9
  rdi : s.regValue .rdi = initial.regValue .r8
  capacity : (localWord initial 168).Word64At s.external (BitVec.ofNat 64 (length + 16))
  pointer : (localWord initial 160).Word64At s.external (initial.regValue .r8)

set_option maxHeartbeats 600000 in
theorem header_to_dispatch [Bindings] {initial s : RamState} {key : Vector UInt8 32}
    {length : Nat} (hs : BeforeHeader initial s key length) (st : EntryStack initial)
    (outside : ¬ InProgram (returnBoundary initial).rip) (bound : length < 2^32) :
    ∃ t, Advances (returnBoundary initial) 8 s t ∧ BeforeCopy initial t key length := by
  obtain ⟨u, au, tu, ripu, capu, ptru, _⟩ := write_header st hs.grows outside
    ⟨hs.ready, hs.code, AgreesExcept.refl _ _⟩ hs.rip hs.rsp
  have commonu : Common initial u key := hs.toCommon.stack_step st tu (by simp [headerChanges]) (by
    intro c hc a ha
    simp only [headerChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ha.elim
    all_goals obtain ⟨i, hi, rfl⟩ := ha
    all_goals exact stack_component_bounds st (by omega) (by omega) hi)
  have ru (r : BitVec 5) : rd u r = rd s r := tu.agrees.read (by simp [headerChanges])
  have lu : rd u 13 = BitVec.ofNat 64 length := (ru 13).trans hs.r13
  obtain ⟨t, advt, tt, ript, zt⟩ := check_length outside
    ⟨commonu.ready, commonu.code, AgreesExcept.refl _ _⟩ ripu lu bound
  have commont : Common initial t key := commonu.stack_step st tt (by simp [lengthChanges]) (by
    intro c hc a ha
    simp only [lengthChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact ha.elim)
  have rt (r : BitVec 5) (hr : r ≠ 5) : rd t r = rd s r :=
    (tt.agrees.read (by simp [lengthChanges]; exact hr)).trans (ru r)
  have wt (a : BitVec 64) : wd t a = wd u a := by
    apply gload tt.agrees
    intro c hc i hi
    simp only [lengthChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact fun h => h
  have word {k : Nat} {v : BitVec 64} (hk : 8 ≤ k) (hk' : k ≤ 1104)
      (hw : wd u (stackPtr initial - BitVec.ofNat 64 k) = v) :
      (localWord initial k).Word64At t.external v := by
    apply word64At_of_memLoad
      (slot_writable st commont.grows hk hk').mem
      ((wt _).trans hw)
    apply BitVec.eq_of_toNat_eq
    rw [slot_toNat0 (by have := st.room; omega)]
    change ((stackPtr initial).toNat - k) % 2^64 = _
    exact Nat.mod_eq_of_lt (by have := (stackPtr initial).isLt; omega)
  refine ⟨t, au.trans advt, ⟨commont, ript, ?_, zt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact sp_keep tt.agrees (by simp [lengthChanges])
      (sp_keep tu.agrees (by simp [headerChanges]) hs.rsp)
  · exact (rt 12 (by decide)).trans hs.r12
  · exact (rt 13 (by decide)).trans hs.r13
  · exact (rt 14 (by decide)).trans hs.r14
  · exact (rt 15 (by decide)).trans hs.r15
  · exact (rt 3 (by decide)).trans hs.rbx
  · exact (rt 7 (by decide)).trans hs.rdi
  · exact word (by omega) (by omega) (capu.trans hs.rbp)
  · exact word (by omega) (by omega) (ptru.trans hs.rdi)

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
