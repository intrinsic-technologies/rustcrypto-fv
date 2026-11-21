import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

def copyComponents (initial : RamState) (destination count : Nat) : List Component :=
  [.reg 6, .reg 7, .reg 1, .mem (stackPtr initial - BitVec.ofNat 64 destination) (8 * count), .rip]

theorem stack_copy [Bindings] {initial t : RamState} {count source destination codeOffset : Nat}
    {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre initial boundary bytes) (state : Frame initial t)
    (positive : 0 < count) (sourceBound : source ≤ 3360) (sourceEnd : 8 * count ≤ source + 8)
    (destinationBound : destination ≤ 3360) (saved : 8 * count + 48 ≤ destination)
    (apart : source + 8 * count ≤ destination ∨ destination + 8 * count ≤ source)
    (codeBound : codeOffset + 3 < 118431)
    (code : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (src : t.regValue .rsi = stackPtr initial - BitVec.ofNat 64 source)
    (dst : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 destination)
    (length : t.regValue .rcx = BitVec.ofNat 64 count) :
    ∃ u, Advances boundary count t u ∧ Frame initial u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) ∧
      AgreesExcept (copyComponents initial destination count) t u ∧
      ∀ i < 8 * count,
        u.external[stackPtr initial - BitVec.ofNat 64 destination + BitVec.ofNat 64 i]? =
          t.external[stackPtr initial - BitVec.ofNat 64 source + BitVec.ofNat 64 i]? := by
  have hn : (rcx.read t).toNat = count := by
    change (t.regValue .rcx).toNat = count
    rw [length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hr : MemReadable t (rsi.read t) (8 * count) := by
    change MemReadable t (t.regValue .rsi) (8 * count)
    rw [src]
    exact readable_of_grow (stack_sub_readable pre.stack sourceBound sourceEnd) state.allocated
  have hw : Writable t (rdi.read t) (8 * count) := by
    change Writable t (t.regValue .rdi) (8 * count)
    rw [dst]
    have readable := readable_of_grow
      (stack_sub_readable pre.stack destinationBound (by omega : 8 * count ≤ destination + 8)) state.allocated
    refine ⟨readable, tables_of_not_reserved (by omega) readable.low ?_⟩
    intro i hi reserved
    exact pre.avoids _ (by simp) _ (ScalarFrame.stack_contains pre.toCalleePre
      destinationBound (by omega) ⟨i, hi, rfl⟩) (.inr reserved)
  have disjoint : (rsi.read t).toNat + 8 * count ≤ (rdi.read t).toNat ∨
      (rdi.read t).toNat + 8 * count ≤ (rsi.read t).toNat := by
    change (t.regValue .rsi).toNat + 8 * count ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 8 * count ≤ (t.regValue .rsi).toNat
    rw [src, dst, stack_sub_toNat pre.stack sourceBound, stack_sub_toNat pre.stack destinationBound]
    have bounds := stack_bounds pre.stack
    omega
  have noCode : RangeApart (rdi.read t) (8 * count)
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 3 := by
    change RangeApart (t.regValue .rdi) _ _ _
    rw [dst]
    intro i hi j hj eq
    apply pre.avoids _ (by simp) _ (ScalarFrame.stack_contains pre.toCalleePre
      destinationBound (by omega) ⟨i, hi, rfl⟩)
    apply Or.inl
    rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset + j) (by omega)
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory
    rip state.directionFlag.df hn hr hw disjoint noCode
  obtain ⟨run, ready, effect, bytes⟩ :=
    P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution
      state.bindingsSupported.stringStride (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) codeOffset _ (by change codeOffset + 3 ≤ 118431; omega) code) pc hn
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset _ (by omega)))
      (by
        change Extracted.textAddress + BitVec.ofNat 64 codeOffset + BitVec.ofNat 64 3 ≠ _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset (codeOffset + 3) codeBound))
  simp only [Nat.max_eq_left (by omega : 1 ≤ count)] at run ready effect bytes
  generalize hu : nextStates count t = u at run ready effect bytes
  have frame : AgreesExcept (copyComponents initial destination count) t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t = _ from dst, copyComponents]
      using effect.agrees
  have writes : WritesWithin (copyComponents initial destination count)
      #v[registerRegion initial .rdi 80, ScalarFrame.workRegion initial 3360] := by
    intro c hc a ha
    simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨ScalarFrame.workRegion initial 3360, by simp,
      ScalarFrame.work_contains pre.toCalleePre destinationBound saved ha⟩
  refine ⟨u, run, state.after_effect pre.toCalleePre (by decide) ready frame writes
    (by simp [copyComponents]), effect.rip, frame, ?_⟩
  simpa only [show rdi.read t = _ from dst, show rsi.read t = _ from src] using bytes

end P256.Proofs.Sec1.Affine.Compressed.Finish
