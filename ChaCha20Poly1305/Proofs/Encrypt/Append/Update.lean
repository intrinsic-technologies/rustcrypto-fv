import ChaCha20Poly1305.Proofs.Encrypt.Append.Tail

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

def appendUpdateChanges (s : RamState) : List Component :=
  [.reg 15, .flags, .rip, .mem (s.regValue .rdi + BitVec.ofNat 64 16) 8]

theorem append_update [Bindings] {s u : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} {boundary : ReturnBoundary}
    (pre : AppendPre s buffer length tag) (outside : ¬ InProgram boundary.rip)
    (grow : Grows s u) (ready : ReadyToStep u) (code : CodeIn Extracted.programImage u)
    (rip : u.RIP = 0x101fe2) (desc : rd u 14 = s.regValue .rdi)
    (len : rd u 15 = BitVec.ofNat 64 length) (count : rd u 3 = 16) :
    ∃ v, Advances boundary 2 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      v.RIP = 0x101fe9 ∧ AgreesExcept (appendUpdateChanges s) u v ∧
      (⟨(s.regValue .rdi).toNat + 16, 8⟩ : MemoryRegion).Word64At v.external
        (BitVec.ofNat 64 (length + 16)) := by
  have T0 : GTrack [.reg 15, .flags, .rip] u u := ⟨ready, code, AgreesExcept.refl _ _⟩
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (add_r64_r64_effect_step 0x101fe2 0x49 0xdf (by unfold RexWPrefix; decide) (by decide))
    T0 (program_text_slice T0.code 0x1fe2 3 (by decide +kernel)) rip
    (code_ne_boundary outside 0x1fe5 (by omega)) (by fits [addR64R64Effect_components])
  change (addR64R64Effect 0x101fe2 15 3 u).Holds u u1 at e1
  have n1 : rd u1 15 = BitVec.ofNat 64 (length + 16) := by
    rw [show rd u1 15 = rd u 15 + rd u 3 from e1.writes, len, count, BitVec.ofNat_add]
    rfl
  have d1 : rd u1 14 = s.regValue .rdi := (e1.agrees.read (by simp)).trans desc
  have A1 : ∀ x, (AddrMode.base 14 (.d8 16)).addr u1 x = s.regValue .rdi + BitVec.ofNat 64 16 := by
    intro x
    change rd u1 14 + (16 : BitVec 8).signExtend 64 = _
    rw [d1]
    rfl
  have writable := output_writable pre.descriptor (pre.separation.2.2 _ (by simp))
  have descriptor : Common.WritableRange s (s.regValue .rdi) 24 := by
    simpa only [appendDescriptor, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
        writable
  have initial := descriptor.slice 16 8 (by omega)
  have hw : Common.WritableRange u1 (s.regValue .rdi + BitVec.ofNat 64 16) 8 :=
    ⟨⟨initial.readable.low, fun i hi => e1.agrees.grow _ (grow _ (initial.readable.mem i hi))⟩,
      initial.tables, initial.code⟩
  have store : StorePre 0x101fe5 4 (storeAddrAt 0x101fe5 (.base 14 (.d8 16)) 4) 8 u1 := by
    refine ⟨e1.rip, ?_, ?_⟩
    · rw [storeAddrAt, A1]
      exact Poly1305.Callee101ce0.writableRange_memWritable hw (by omega)
    · rw [storeAddrAt, A1]
      intro i hi j hj eq
      exact hw.code i hi (eq.symm ▸ code_inProgram 0x1fe5 4 (by omega) j hj)
  obtain ⟨v, a2, rv, cv, e2⟩ := step_run
    (mov_m64_r64_effect_step 0x101fe5 0x4d (by unfold RexWPrefix; decide) 7
      (.base 14 (.d8 16)) (by decide) (by decide) (by decide))
    T1.ready T1.code (program_text_slice T1.code 0x1fe5 4 (by decide +kernel)) store
    (code_ne_boundary outside 0x1fe9 (by omega)) (by
      intro comp hc a hcover
      simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rw [storeAddrAt, A1] at hcover
        obtain ⟨i, hi, rfl⟩ := hcover
        exact hw.code i hi
      · exact hcover.elim)
  change (movM64R64Effect 0x101fe5 15 (.base 14 (.d8 16)) u1).Holds u1 v at e2
  have stored : wd v (s.regValue .rdi + BitVec.ofNat 64 16) = BitVec.ofNat 64 (length + 16) := by
    have h : wd v ((AddrMode.base 14 (.d8 16)).addr u1 _) = rd u1 15 := e2.writes
    rw [A1] at h
    exact h.trans n1
  refine ⟨v, a1.trans a2, rv, cv, e2.rip, ?_, ?_⟩
  · apply (e1.agrees.trans e2.agrees).mono
    intro comp hc
    simp only [List.mem_append, addR64R64Effect_components,
      movM64R64Effect_components, storeAddrAt] at hc
    rw [A1] at hc
    simpa [appendUpdateChanges, or_assoc, or_left_comm, or_comm] using hc
  · apply word64At_of_memLoad
      (fun i hi => e2.agrees.grow _ (hw.readable.mem i hi)) stored
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem append_update_keeps [Bindings] {s u v : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} {r : MemoryRegion} {a : BitVec 64}
    (pre : AppendPre s buffer length tag) (ag : AgreesExcept (appendUpdateChanges s) u v)
    (disjoint : (appendDescriptor s).Disjoint r) (inside : r.Contains a.toNat) :
    v.external[a]? = u.external[a]? := by
  have hb : (s.regValue .rdi).toNat + 24 < 2 ^ 32 := pre.descriptor.1
  apply ag.byte
  intro comp hc hcover
  simp only [appendUpdateChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨i, hi, rfl⟩ := hcover
  apply disjoint _ ?_ inside
  change (s.regValue .rdi).toNat ≤ _ ∧ _ < (s.regValue .rdi).toNat + 24
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem append_update_frame [Bindings] {s u v : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} (pre : AppendPre s buffer length tag)
    (ag : AgreesExcept (appendUpdateChanges s) u v) :
    MemoryWriteFrame u v #v[⟨(s.regValue .rdi).toNat + 16, 8⟩] := by
  have hb : (s.regValue .rdi).toNat + 24 < 2 ^ 32 := pre.descriptor.1
  apply ag.memoryWriteFrame
  intro comp hc a hcover
  simp only [appendUpdateChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨i, hi, rfl⟩ := hcover
  refine ⟨⟨(s.regValue .rdi).toNat + 16, 8⟩, by simp, ?_⟩
  change (s.regValue .rdi).toNat + 16 ≤ _ ∧ _ < (s.regValue .rdi).toNat + 16 + 8
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end ChaCha20Poly1305.Proofs.Encrypt
