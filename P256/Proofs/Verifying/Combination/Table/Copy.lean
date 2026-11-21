import P256.Proofs.Verifying.Combination.Table.Memory
import P256.Proofs.Common.Instructions.RepMovsqAny
import P256.Proofs.Program.Code
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copy_to_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {value : Projective}
    (pre : TablePre s boundary cursor point) (state : FrameState s t cursor)
    (codeOffset : Nat) (codeBound : codeOffset + 3 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (destination : Nat) (destBound : destination ≤ 1096) (destSaved : 128 ≤ destination)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 destination)
    (count : t.regValue .rcx = 12)
    (source : MemReadable t (t.regValue .rsi) 96)
    (disjoint : (t.regValue .rsi).toNat + 96 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 96 ≤ (t.regValue .rsi).toNat)
    (input : ProjectiveAt t (t.regValue .rsi) value) :
    ∃ u, Advances boundary 12 t u ∧ FrameState s u cursor ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) ∧
      ProjectiveAt u (stackPtr s - BitVec.ofNat 64 destination) value ∧
      AgreesExcept [.reg 6, .reg 7, .reg 1,
        .mem (stackPtr s - BitVec.ofNat 64 destination) 96, .rip] t u := by
  have hn : (rcx.read t).toNat = 12 := by change (t.regValue .rcx).toNat = 12; rw [count]; rfl
  have dest : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) 96 := by
    rw [dst]
    have readable := P256.Proofs.Program.readable_of_grow
      (P256.Proofs.Program.stack_sub_readable pre.stack (offset := destination) (len := 96)
        (by omega) (by omega)) state.allocated
    refine ⟨readable, ?_⟩
    apply tables_of_not_reserved (by decide) readable.low
    intro i hi hreserved
    apply pre.avoids (Stack.region s 2120) (by simp) _ ?_ (.inr hreserved)
    exact P256.Proofs.Program.ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) ⟨i, hi, rfl⟩
  have apart : RangeApart (rdi.read t) 96
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 3 := by
    change RangeApart (t.regValue .rdi) 96 _ 3
    rw [dst]
    intro i hi j hj he
    apply pre.avoids (Stack.region s 2120) (by simp) _
      (P256.Proofs.Program.ScalarFrame.stack_contains pre.toCalleePre
        (offset := destination) (len := 96) (by omega) (by omega) ⟨i, hi, rfl⟩) (.inl ?_)
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset + j) (by omega)
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory rip state.directionFlag.df hn source dest disjoint apart
  have next : Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) =
      Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 3) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  obtain ⟨run, ready, effect, bytes⟩ := P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution pre.bindingsSupported.stringStride
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) codeOffset [0xf3, 0x48, 0xa5]
      (by change codeOffset + 3 ≤ 118431; omega) codeBytes) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset codeOffset (by omega)))
    (boundary_ne_program pre.outerBoundary (by rw [next]; exact inProgram_of_textOffset _ codeBound))
  simp only [show max 12 1 = 12 from rfl] at run ready effect bytes
  generalize hu : nextStates 12 t = u at run ready effect bytes
  have frame : AgreesExcept [.reg 6, .reg 7, .reg 1,
      .mem (stackPtr s - BitVec.ofNat 64 destination) 96, .rip] t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t =
      stackPtr s - BitVec.ofNat 64 destination from dst, Nat.reduceMul] using effect.agrees
  have writes : WritesWithin [.reg 6, .reg 7, .reg 1,
      .mem (stackPtr s - BitVec.ofNat 64 destination) 96, .rip]
      #v[registerRegion s .rdi 768, workRegion s] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨workRegion s, by simp, work_contains pre (by omega) destSaved ha⟩
  refine ⟨u, run, after pre state ready frame writes (by simp) (by simp) (by simp), effect.rip, ?_, frame⟩
  rw [← dst]
  exact input.of_bytes_eq bytes

theorem copy_cells [Bindings] {s t : RamState} {boundary : ReturnBoundary} {cursor point : BitVec 64}
    {cells : Cells} {value : Projective} (pre : TablePre s boundary cursor point)
    (state : Memory s t cursor point cells) (slot : Slot)
    (codeOffset : Nat) (codeBound : codeOffset + 3 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 (offset slot))
    (count : t.regValue .rcx = 12)
    (source : MemReadable t (t.regValue .rsi) 96)
    (disjoint : (t.regValue .rsi).toNat + 96 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 96 ≤ (t.regValue .rsi).toNat)
    (input : ProjectiveAt t (t.regValue .rsi) value) :
    ∃ u, Advances boundary 12 t u ∧ Memory s u cursor point (writeCell cells slot value) ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) ∧
      AgreesExcept [.reg 6, .reg 7, .reg 1,
        .mem (stackPtr s - BitVec.ofNat 64 (offset slot)) 96, .rip] t u := by
  have bounds := offset_bounds slot
  obtain ⟨u, run, frame, rip, value, agrees⟩ := copy_to_stack pre state.toFrameState
    codeOffset codeBound codeBytes rip (offset slot) (by omega) bounds.1
    dst count source disjoint input
  refine ⟨u, run, state.update frame value ?_ ?_, rip, agrees⟩
  · intro off len ho hl apart i hi
    apply agrees_byte pre agrees ?_ (by omega) ho hl apart hi
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ha
  · apply cursor_read_of_frame pre
    apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨Stack.region s 2120, by simp,
      P256.Proofs.Program.ScalarFrame.stack_contains pre.toCalleePre (by have := offset_bounds slot; omega)
        (by have := offset_bounds slot; omega) ha⟩

end P256.Proofs.Verifying.Combination.Table
