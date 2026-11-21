import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Sec1.Affine.Identity.Data
import P256.Proofs.Sec1.Affine.Representation
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Field

theorem constant_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) {offset : Nat}
    (high : offset ≤ 760) (low : 72 + 48 ≤ offset) :
    0x202df8 + 72 ≤ (stackPtr s - BitVec.ofNat 64 offset).toNat ∨
      (stackPtr s - BitVec.ofNat 64 offset).toNat + 72 ≤ 0x202df8 := by
  have hs := stack_bounds pre.stack
  have hn : (stackPtr s - BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat - offset :=
    stack_sub_toNat pre.stack (by omega)
  by_cases hbefore : 0x202df8 + 72 ≤ (stackPtr s - BitVec.ofNat 64 offset).toNat
  · exact .inl hbefore
  right
  apply Nat.le_of_not_lt
  intro hafter
  let a := max 0x202df8 (stackPtr s - BitVec.ofNat 64 offset).toNat
  have ha : a < 2^64 := by dsimp only [a]; have := (stackPtr s - BitVec.ofNat 64 offset).isLt; omega
  have he : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
  have him : InProgram (BitVec.ofNat 64 a) := by
    have h := identity_byte_inProgram (i := a - 0x202df8) (by dsimp only [a]; omega)
    have hadd : 0x202df8 + BitVec.ofNat 64 (a - 0x202df8) = BitVec.ofNat 64 a := by
      rw [show (0x202df8 : BitVec 64) = BitVec.ofNat 64 0x202df8 from rfl,
        ← BitVec.ofNat_add, Nat.add_sub_of_le]
      exact Nat.le_max_left _ _
    rwa [hadd] at h
  apply pre.avoids (Stack.region s 3360) (by simp) (BitVec.ofNat 64 a) _ (.inl him)
  change (Stack.region s 3360).start ≤ _ ∧ _ <
    (Stack.region s 3360).start + (Stack.region s 3360).size
  rw [he, stack_region_end]
  change 3360 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 at hs
  change (stackPtr s).toNat - 3360 ≤ a ∧ a < (stackPtr s).toNat + 8
  dsimp only [a]
  omega

def constantComponents (s : RamState) (offset : Nat) : List Component :=
  [.reg 6, .reg 7, .reg 1, .mem (stackPtr s - BitVec.ofNat 64 offset) 72, .rip]

theorem copy_constants [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    {offset : Nat} (high : offset ≤ 760) (low : 72 + 48 ≤ offset)
    (codeOffset : Nat) (codeBound : codeOffset + 3 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset) (src : t.regValue .rsi = 0x202df8)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 offset) (count : t.regValue .rcx = 9) :
    ∃ u, Advances boundary 9 t u ∧ Frame s u ∧ u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) ∧
      AffineAt u (stackPtr s - BitVec.ofNat 64 offset) .infinity ∧ AgreesExcept (constantComponents s offset) t u := by
  have hn : (rcx.read t).toNat = 9 := by change (t.regValue .rcx).toNat = 9; rw [count]; rfl
  have source : MemReadable t (rsi.read t) 72 := by
    change MemReadable t (t.regValue .rsi) 72
    rw [src]
    exact identity_readable state.loaded
  have dest : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (rdi.read t) 72 := by
    change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) 72
    rw [dst]
    have readable := readable_of_grow
      (stack_sub_readable pre.stack (offset := offset) (len := 72) (by omega) (by omega))
      state.allocated
    refine ⟨readable, tables_of_not_reserved (by decide) readable.low ?_⟩
    intro i hi reserved
    exact pre.avoids _ (by simp) _
      (ScalarFrame.stack_contains pre.toCalleePre (offset := offset) (len := 72) (by omega) (by omega) ⟨i, hi, rfl⟩)
      (.inr reserved)
  have disjoint : (rsi.read t).toNat + 72 ≤ (rdi.read t).toNat ∨
      (rdi.read t).toNat + 72 ≤ (rsi.read t).toNat := by
    change (t.regValue .rsi).toNat + 72 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 72 ≤ (t.regValue .rsi).toNat
    rw [src, dst]
    exact constant_disjoint pre high low
  have apart : RangeApart (rdi.read t) 72
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 3 := by
    change RangeApart (t.regValue .rdi) 72 _ 3
    rw [dst]
    intro i hi j hj he
    apply pre.avoids _ (by simp) _
      (ScalarFrame.stack_contains pre.toCalleePre (offset := offset) (len := 72) (by omega) (by omega) ⟨i, hi, rfl⟩)
    left
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset + j) (by omega)
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory rip state.directionFlag.df hn source dest disjoint apart
  obtain ⟨run, ready, effect, bytes⟩ := P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution pre.bindingsSupported.stringStride
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) codeOffset [0xf3,0x48,0xa5]
      (by change codeOffset + 3 ≤ 118431; omega) codeBytes) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset codeOffset (by omega)))
    (by
      apply boundary_ne_program pre.outerBoundary
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
        inProgram_of_textOffset (codeOffset + 3) codeBound)
  simp only [show max 9 1 = 9 from rfl] at run ready effect bytes
  generalize hu : nextStates 9 t = u at run ready effect bytes
  have agrees : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (stackPtr s - BitVec.ofNat 64 offset) 72, .rip] t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t = stackPtr s - BitVec.ofNat 64 offset from dst,
      Nat.reduceMul] using effect.agrees
  have writes : WritesWithin [.reg 6, .reg 7, .reg 1, .mem (stackPtr s - BitVec.ofNat 64 offset) 72, .rip]
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 3360] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨ScalarFrame.workRegion s 3360, by simp,
      ScalarFrame.work_contains pre.toCalleePre (by omega) (by omega) ha⟩
  refine ⟨u, run, state.after_effect pre.toCalleePre (by decide) ready agrees writes (by simp),
    effect.rip, ?_, agrees⟩
  apply (identity_at state.loaded).of_bytes_eq
  intro i hi
  have hb := bytes i (by omega)
  change u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
    t.external[t.regValue .rsi + BitVec.ofNat 64 i]? at hb
  simpa only [src, dst] using hb


end P256.Proofs.Sec1.Affine.Compressed.Finish
