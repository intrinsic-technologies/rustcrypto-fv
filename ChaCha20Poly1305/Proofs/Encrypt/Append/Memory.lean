import ChaCha20Poly1305.Proofs.Encrypt.Append.Call

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper

theorem output_writable {s : RamState} {r : MemoryRegion} (h : ValidOutput s r)
    (ha : r.Avoids (fun a => InProgram a ∨ pageTables.Contains a.toNat)) :
    Common.WritableRange s (BitVec.ofNat 64 r.start) r.size := by
  have hb : r.start + r.size < 2 ^ 32 := h.1
  have hn : ∀ i < r.size,
      (BitVec.ofNat 64 r.start + BitVec.ofNat 64 i).toNat = r.start + i := by
    intro i hi
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [BitVec.toNat_ofNat]; omega
  · intro i hi
    obtain ⟨b, he⟩ := h.2 (BitVec.ofNat 64 r.start + BitVec.ofNat 64 i) (by
      rw [hn i hi]; exact ⟨by omega, by omega⟩)
    simp only [he, Option.isSome_some]
  · intro i hi hp
    exact ha _ (by rw [hn i hi]; exact ⟨by omega, by omega⟩) (Or.inr hp)
  · intro i hi hp
    exact ha _ (by rw [hn i hi]; exact ⟨by omega, by omega⟩) (Or.inl hp)

theorem append_memcpy_pre [Bindings] {s u c : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} (pre : AppendPre s buffer length tag)
    (atCopy : AppendAtCopy s u buffer length) (rip : c.RIP = 0x102dc0)
    (rsp : stackPtr c = stackPtr s - BitVec.ofNat 64 48)
    (ret : returnBoundary c = { rip := 0x101fe2, rsp := stackPtr s - BitVec.ofNat 64 40 })
    (push : AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 48) 8, .rip] u c) :
    MemoryContracts.MemcpyPre c := by
  have grows := atCopy.agrees.trans push
  have di : rdi.read c = buffer + BitVec.ofNat 64 length := (push.read (by simp)).trans atCopy.rdi
  have dx : MemoryRoutines.rdx.read c = 16 := (push.read (by simp)).trans atCopy.rdx
  have si : rsi.read c = s.regValue .rsi := (push.read (by simp)).trans atCopy.rsi
  have hb : buffer.toNat + length + 16 < 2 ^ 32 := pre.lengthBound
  have dn : (buffer + BitVec.ofNat 64 length).toNat = buffer.toNat + length := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have srcBound : (s.regValue .rsi).toNat + 16 < 2 ^ 32 := pre.source.1
  have dstStack : (appendDestination buffer length).Disjoint (Stack.region s 48) :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp pre.separation.1).2).1 _ (by simp)
  have dstSrc : (appendDestination buffer length).Disjoint (appendSource s) :=
    pre.separation.2.1 _ (by simp) _ (by simp)
  have writable := output_writable pre.destination (pre.separation.2.2 _ (by simp))
  have da : BitVec.ofNat 64 (appendDestination buffer length).start =
      buffer + BitVec.ofNat 64 length := by
    change BitVec.ofNat 64 (buffer.toNat + length) = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have df := grows.directionFlagClear
    (by simp [appendPushChanges, appendBodyChanges]) pre.directionFlagUnset
  refine ⟨⟨rip, df.df, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [di, dx]
    change Common.WritableRange c (buffer + BitVec.ofNat 64 length) 16
    have hw := writable.of_agrees grows
    rw [da] at hw
    exact hw
  · rw [rsp]
    exact stack_slot_readable pre.stack grows.grow (by omega)
  · rw [di, dx, rsp]
    change RangeApart (buffer + BitVec.ofNat 64 length) 16
      (stackPtr s - BitVec.ofNat 64 48) 8
    intro i hi j hj he
    apply dstStack (buffer + BitVec.ofNat 64 length + BitVec.ofNat 64 i).toNat
    · change buffer.toNat + length ≤ _ ∧ _ < buffer.toNat + length + 16
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at *
      omega
    · rw [he]
      exact stack_slot_contains pre.stack (by omega) (by omega)
  · rw [ret]
    change (0x101fe2 : BitVec 64).toNat < 2 ^ 32
    decide
  · rw [ret]
    change (0x101fe2 : BitVec 64).toNat < (0x102dc0 : BitVec 64).toNat ∨ _
    exact Or.inl (by decide)
  · rw [si, dx]
    change MemReadable c (s.regValue .rsi) 16
    refine ⟨by omega, ?_⟩
    intro i hi
    apply grows.grow
    have h := hasBytes_isSome pre.source.2 hi
    simpa only [appendSource, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using h
  · rw [si, di, dx, dn]
    have sep := region_sep dstSrc (by change 0 < 16; decide) (by change 0 < 16; decide)
    change buffer.toNat + length + 16 ≤ (s.regValue .rsi).toNat ∨
      (s.regValue .rsi).toNat + 16 ≤ buffer.toNat + length at sep
    exact sep.symm

theorem append_memcpy [bindings : Bindings] {s u : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} {boundary : ReturnBoundary}
    (pre : AppendPre s buffer length tag) (outside : ¬ InProgram boundary.rip)
    (atCopy : AppendAtCopy s u buffer length) :
    ∃ fuel c t, Advances boundary fuel u t ∧ MemoryContracts.MemcpyResult c t ∧
      CodeIn Extracted.programImage t ∧ MemoryContracts.MemcpyPre c ∧
      stackPtr c = stackPtr s - BitVec.ofNat 64 48 ∧
      returnBoundary c = { rip := 0x101fe2, rsp := stackPtr s - BitVec.ofNat 64 40 } ∧
      AgreesExcept [.reg 4, .mem (stackPtr s - BitVec.ofNat 64 48) 8, .rip] u c := by
  obtain ⟨c, ac, rc, cc, ipc, spc, ret, push⟩ := append_memcpy_entry pre outside atCopy
  have hp := append_memcpy_pre pre atCopy ipc spc ret push
  obtain ⟨fuel, t, adv, result⟩ := MemoryContracts.memcpy_advances pre.environment.stringStride
    boundary (Core.Absorb.outside_routine outside (by decide) (by decide)) c rc cc hp
    (by rw [ret]; exact code_ne_boundary outside 0x1fe2 (by omega))
  exact ⟨1 + fuel, c, t, ac.trans adv, result, result.toCallResult.codeIn hp.dst cc,
    hp, spc, ret, push⟩

end ChaCha20Poly1305.Proofs.Encrypt
