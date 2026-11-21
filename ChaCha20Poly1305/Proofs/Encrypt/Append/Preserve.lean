import ChaCha20Poly1305.Proofs.Encrypt.Append.Memory

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper

theorem append_memcpy_keeps_stack_word [Bindings] {s u c t : RamState} {buffer : BitVec 64}
    {length k : Nat} {tag : Vector UInt8 16} (pre : AppendPre s buffer length tag)
    (atCopy : AppendAtCopy s u buffer length)
    (push : AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 48) 8, .rip] u c)
    (result : MemoryContracts.MemcpyResult c t) (hk : k ≤ 40) :
    wd t (stackPtr s - BitVec.ofNat 64 k) = wd u (stackPtr s - BitVec.ofNat 64 k) := by
  obtain ⟨hroom, htop⟩ := stack_bounds pre.stack
  have hb : buffer.toNat + length + 16 < 2 ^ 32 := pre.lengthBound
  have dstStack : (appendDestination buffer length).Disjoint (Stack.region s 48) :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp pre.separation.1).2).1 _ (by simp)
  have sep := region_sep dstStack (by change 0 < 16; decide) (by
    change 0 < (stackPtr s).toNat + 8 - ((stackPtr s).toNat - 48); omega)
  change buffer.toNat + length + 16 ≤ (stackPtr s).toNat - 48 ∨
    (stackPtr s).toNat - 48 + ((stackPtr s).toNat + 8 - ((stackPtr s).toNat - 48)) ≤
      buffer.toNat + length at sep
  have di : rdi.read c = buffer + BitVec.ofNat 64 length := (push.read (by simp)).trans atCopy.rdi
  have dx : MemoryRoutines.rdx.read c = 16 := (push.read (by simp)).trans atCopy.rdx
  have ag := push.trans result.agrees
  simp only [MemoryRoutines.callChanges, di, dx] at ag
  apply gload ag
  intro comp hc i hi
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals try exact nonmem_not_covers rfl _
  · exact slot_not_covers hi (by omega) (by omega) (by omega)
  · change ¬ (Component.mem (buffer + BitVec.ofNat 64 length) 16).Covers _
    apply mem_not_covers
    · rw [slot_toNat (by omega) htop (by omega)]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega

theorem append_call_frame [Bindings] {s u c : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} (pre : AppendPre s buffer length tag)
    (atCopy : AppendAtCopy s u buffer length)
    (push : AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 48) 8, .rip] u c) :
    MemoryWriteFrame s c #v[Stack.region s 48] := by
  have frame : MemoryWriteFrame u c #v[Stack.region s 48] := by
    apply push.memoryWriteFrame
    intro comp hc a hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcover.elim
    · obtain ⟨i, hi, rfl⟩ := hcover
      exact ⟨Stack.region s 48, by simp, stack_slot_contains pre.stack (by omega) (by omega)⟩
    · exact hcover.elim
  intro a ha
  exact (frame a ha).trans (atCopy.frame a ha)

theorem append_memcpy_tag [Bindings] {s u c t : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} (pre : AppendPre s buffer length tag)
    (atCopy : AppendAtCopy s u buffer length)
    (push : AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 48) 8, .rip] u c)
    (result : MemoryContracts.MemcpyResult c t) :
    (appendDestination buffer length).HasBytes t.external ⟨tag.toArray⟩ := by
  have di : rdi.read c = buffer + BitVec.ofNat 64 length := (push.read (by simp)).trans atCopy.rdi
  have dx : MemoryRoutines.rdx.read c = 16 := (push.read (by simp)).trans atCopy.rdx
  have si : rsi.read c = s.regValue .rsi := (push.read (by simp)).trans atCopy.rsi
  have frame := append_call_frame pre atCopy push
  have disjoint := pre.separation.2.1 (Stack.region s 48) (by simp) (appendSource s) (by simp)
  have bound : (s.regValue .rsi).toNat + 16 < 2 ^ 32 := pre.source.1
  refine ⟨by change tag.toArray.size = 16; exact tag.size_toArray, ?_⟩
  intro i
  have hi : i.val < 16 := by
    have h := i.isLt
    change i.val < tag.toArray.size at h
    rw [tag.size_toArray] at h
    exact h
  have copied := result.copy i.val (by rw [dx]; exact hi)
  rw [di, si] at copied
  have kept : c.external[s.regValue .rsi + BitVec.ofNat 64 i.val]? =
      s.external[s.regValue .rsi + BitVec.ofNat 64 i.val]? := by
    apply frame
    intro r hr hcontains
    have he : r = Stack.region s 48 := by simpa using hr
    subst r
    apply disjoint _ hcontains
    change (s.regValue .rsi).toNat ≤ _ ∧ _ < (s.regValue .rsi).toNat + 16
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [kept] at copied
  have original := pre.source.2.2 i
  have dstAddr : BitVec.ofNat 64 ((appendDestination buffer length).start + i.val) =
      buffer + BitVec.ofNat 64 length + BitVec.ofNat 64 i.val := by
    simp only [appendDestination, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have srcAddr : BitVec.ofNat 64 ((appendSource s).start + i.val) =
      s.regValue .rsi + BitVec.ofNat 64 i.val := by
    simp only [appendSource, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
  rw [dstAddr, copied, ← srcAddr]
  exact original

theorem append_memcpy_frame [Bindings] {s u c t : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} (pre : AppendPre s buffer length tag)
    (atCopy : AppendAtCopy s u buffer length)
    (push : AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 48) 8, .rip] u c)
    (result : MemoryContracts.MemcpyResult c t) :
    MemoryWriteFrame s t #v[appendDestination buffer length, Stack.region s 48] := by
  have di : rdi.read c = buffer + BitVec.ofNat 64 length := (push.read (by simp)).trans atCopy.rdi
  have dx : MemoryRoutines.rdx.read c = 16 := (push.read (by simp)).trans atCopy.rdx
  have hb : buffer.toNat + length + 16 < 2 ^ 32 := pre.lengthBound
  have dn : (buffer + BitVec.ofNat 64 length).toNat = buffer.toNat + length := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have fc := append_call_frame pre atCopy push
  have ft := result.toCallResult.frame (by rw [di, dx, dn]; exact Nat.le_of_lt hb)
  have de : MemoryRoutines.destination c = appendDestination buffer length := by
    simp only [MemoryRoutines.destination, di, dx, dn, appendDestination]
    rfl
  intro a ha
  refine (ft a ?_).trans (fc a ?_)
  · intro r hr
    have he : r = MemoryRoutines.destination c := by simpa using hr
    subst r
    rw [de]
    exact ha _ (by simp)
  · intro r hr
    have he : r = Stack.region s 48 := by simpa using hr
    subst r
    exact ha _ (by simp)

end ChaCha20Poly1305.Proofs.Encrypt
